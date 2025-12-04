module Clase11.Cliente

open Container
open Clase11.Listas
open FStar.Tactics

let test (#t : Type) {| container int t |} () =
  let l : t = empty in
  empty_ok #int #t ();
  assert (models l TSet.empty);
  ins_ok 2 l TSet.empty;
  let l = ins 2 l in
  del_ok 3 l (TSet.union TSet.empty (TSet.singleton 2));
  let l = del 3 l in
  assert (models l (TSet.intersect (TSet.union TSet.empty (TSet.singleton 2)) (TSet.complement (TSet.singleton 3))));
  mem_ok 2 l (TSet.intersect (TSet.union TSet.empty (TSet.singleton 2)) (TSet.complement (TSet.singleton 3)));
  assert (mem 2 l);
  // ^ demostrable, pero aburrido: hay que llamar los lemas a mano
  ()
