module Clase09

#lang-pulse

open Pulse
open FStar.List.Tot

noeq
type node (t:Type0) = {
    head : t;
    tail : llist t;
}
and llist (t:Type0) = ref (node t)

let rec is_list #t ([@@@mkey] x : llist t) (l : list t)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (x == null)
    | head::tl -> 
      exists* (tail : llist t).
        pts_to x { head; tail } **
        is_list tail tl

let ambos (p q : slprop) = p ** q

fn set0 (x y : ref int)
  requires ambos (x |-> 1) (y |-> 2)
  ensures  ambos (x |-> 3) (y |-> 2)
{
  unfold ambos;
  x := 3;
  fold ambos (x |-> 3) (y |-> 2);
  ();
}

fn alloc_list #t ()
  requires emp
  returns  l : llist t
  ensures  is_list l []
{
  let r : ref (node t) = null;
  assert pure (r == null);
  fold (is_list r []);
  assert (is_list r []);
  r
}

fn push #t (x : t) (l : llist t)
  requires is_list l 's
  returns  l' : llist t
  ensures  is_list l' (x :: 's)
{
  let n : ref (node t) = alloc { head=x; tail=l };
  fold (is_list n (x :: 's));
  n
}

fn pop #t (l : llist t) (#hd : erased t) (#tl : erased (list t))
  requires is_list l (reveal hd :: tl)
  returns  l' : llist t
  ensures  is_list l' tl
{
  unfold is_list;
  let l' = (!l).tail;
  with lv. assert (l |-> {head=reveal hd; tail=lv});
  rewrite each lv as l';
  assume pure (is_full_ref l);
  free l;
  l'
}

fn peek #t (l : llist t) (#hd : erased t) (#tl : erased (list t))
  preserves is_list l (reveal hd :: tl)
  returns   x : t
  ensures   pure (x == hd)
{
  unfold is_list;
  let r = (!l).head;
  fold is_list l (reveal hd :: tl);
  r
}

ghost
fn is_list_null_ref #t (a : llist t) (s : list t)
  requires is_list a s
  requires pure (a == null)
  ensures  is_list a [] ** pure (s == [])
{
  match s {
    [] -> { (); }
    hd :: tl -> {
      unfold is_list;
      pts_to_not_null a;
      unreachable ();
    }
  }
}

ghost
fn is_list_non_null_ref #t (a : llist t) (s : list t)
  requires is_list a s
  requires pure (a =!= null)
  ensures
    exists* h t.
      is_list a (h :: t) ** pure (s == h :: t)
{
  match s {
    [] -> {
      unfold is_list a [];
      unreachable ();
    }
    hd :: tl -> { (); }
  }
}

fn insitu_rev #t (a : llist t) (s : list t)
  requires is_list a s
  returns  b : llist t
  ensures  is_list b (rev s)
{
  let mut a = a;
  let mut b = alloc_list #t ();
  while (not (is_null !a))
    invariant
      live a ** live b **
      (exists* (la lb : list t).
        is_list (!a) la **
        is_list (!b) lb **
        pure (rev la @ lb == rev s))
  {
    with la. assert is_list (!a) la;
    with lb. assert is_list (!b) lb;
    assert pure (rev la @ lb == rev s);
    is_list_non_null_ref (!a) la;
    let v = peek (!a);
    b := push v (!b);
    a := pop (!a);
    assert pure (rev (hd la :: tail la) @ lb == rev s);
    rev_append (hd la :: tail la) lb;
    rev_append [hd la] (tail la);
    append_assoc (rev (tail la)) [hd la] lb;
    assert pure (rev (hd la :: tail la) @ lb == rev (tail la) @ (hd la :: lb));
    assert pure (rev (tail la) @ (hd la :: lb) == rev s);
    ();
    ()
  };
  assert pure (!a == null);
  is_list_null_ref (!a) _;
  assert (is_list (!a) []);
  unfold (is_list (!a) []);
  assert (is_list (!b) (rev s));
  let lb = !b;
  lb;
}
