module Clase10

#lang-pulse
open Pulse
module U32 = FStar.UInt32
module B = Pulse.Lib.Box

(* Suma paralela *)
fn incr_par (x y : ref int)
  requires x |-> 'vx ** y |-> 'vy
  ensures  x |-> ('vx + 1) ** y |-> ('vy + 1)
{
  Pulse.Lib.Par.par
    #(x |-> 'vx) // falta inferencia
    #(x |-> ('vx + 1))
    #(y |-> 'vy)
    #(y |-> ('vy + 1))
    fn () { x := !x + 1; }
    fn () { y := !y + 1; }
}

// Supocisiones sobre la máquina
atomic
fn write_atomic_box (r:B.box U32.t) (x:U32.t) (#n:erased U32.t)
  requires r |-> n
  ensures  r |-> x
{
  admit();
}

// Compare-and-swap
atomic
fn cas_box (r:B.box U32.t) (u v:U32.t) (#i:erased U32.t)
  requires r |-> i
  returns b: bool
  ensures (
    if b
    then r |-> v ** pure (reveal i == u)
    else r |-> i
  )
{
  admit();
}

noeq
type lock = {
  r : B.box U32.t;
  i : iname;
}

let maybe (b:bool) (p:slprop) =
  if b then p else emp

let lock_inv (r:B.box U32.t) (p:slprop) : slprop =
  exists* v.
    r |-> v ** maybe (v = 0ul) p

let lock_alive (l:lock) (p :slprop) =
  inv l.i (lock_inv l.r p)

// El permiso sobre un lock se puede duplicar sin problema.
ghost
fn dup_lock_alive (l:lock) (#p:slprop)
  requires lock_alive l p
  ensures  lock_alive l p ** lock_alive l p
{
  unfold lock_alive l p;
  dup_inv l.i _;
  fold lock_alive l p;
  fold lock_alive l p;
}

// Crear un lock: alocar la referencia + invariante.
fn new_lock (p:slprop)
  requires p
  returns  l : lock
  ensures  lock_alive l p
{
  let r = B.alloc 0ul;
  rewrite p as maybe true p;
  fold lock_inv r p;
  let i = new_invariant (lock_inv r p);

  let l : lock = { r; i };
  rewrite each r as l.r;
  rewrite each i as l.i;
  fold lock_alive l;
  l
}

// assume val p : slprop
// let q = p

// fn test ()
//   requires p
//   ensures  q
// {
//   rewrite p as q;
//   ();
// }
// fn test2 ()
//   requires q
//   ensures  p
// {
//   unfold q;
//   ();
// }


// Intentar adquirir el lock con un CAS.
fn try_acquire (#p:slprop) (l:lock)
  preserves lock_alive l p
  returns  b : bool
  ensures  maybe b p
{
  unfold lock_alive;
  let b = 
    with_invariants bool emp_inames l.i (lock_inv l.r p)
      emp (fun b -> maybe b p)
      fn _ {
        unfold lock_inv;
        with vv. assert l.r |-> vv;
        let b = cas_box l.r 0ul 1ul;
        if b {
          rewrite each vv as 0ul;
          rewrite emp as maybe false p;
          fold lock_inv l.r p;
          b;
        } else {
          fold lock_inv l.r p;
          rewrite emp as maybe false p;
          b;
        }
    };
  fold lock_alive;
  b;
}

// Adquirir el lock (bloqueante).
fn rec acquire (#p:slprop) (l:lock)
  preserves lock_alive l p
  ensures   p
{
  let b = try_acquire l;
  if b {
    unfold maybe;
  } else {
    unfold maybe;
    acquire l;
  }
}

// Soltar el lock.
fn release (#p:slprop) (l:lock)
  preserves lock_alive l p
  requires  p
{
  unfold lock_alive;
  with_invariants unit emp_inames
    l.i (lock_inv l.r p) p (fun _ -> emp)
    fn _ {
      unfold lock_inv;
      with vv. assert l.r |-> vv;
      drop_ (maybe (vv = 0ul) p); // raro...
      rewrite p as maybe true p;
      write_atomic_box l.r 0ul;
      fold lock_inv l.r p;
  };
  fold lock_alive;
}

instance fake_is_send (a : slprop) : is_send a = magic()

fn suma_paralela_mutex ()
{
  let r = alloc 0;
  let l = new_lock (exists* v. r |-> v);
  dup_lock_alive l;
  Pulse.Lib.Par.par
    #(lock_alive l (exists* (v:int). r |-> v))
    #(lock_alive l (exists* (v:int). r |-> v))
    #(lock_alive l (exists* (v:int). r |-> v))
    #(lock_alive l (exists* (v:int). r |-> v))
    fn _ {
      acquire l;
      r := !r + 1;
      release l;
    }
    fn _ {
      acquire l;
      r := !r + 1;
      release l;
    };
  drop_ (lock_alive _ _);
  drop_ (lock_alive _ _);
  ()
}

fn muerto (#p:slprop) (l:lock)
  preserves lock_alive l p
{
  acquire l;
  acquire l;
  release l;
  release l;
}

