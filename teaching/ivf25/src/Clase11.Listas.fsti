module Clase11.Listas

open Container

instance val listas_son_container0 (a:eqtype)
  : container0 a (list a)

instance val listas_son_container_laws (a:eqtype)
  : container_laws a (list a) 

instance listas_son_container (a:eqtype)
  : container a (list a) = {
    ops = _; laws = listas_son_container_laws a;
  }

// val trie (a:Type) : Type
// instance val trie_son_container0 (a:eqtype)
//   : container0 (list a) (trie a)

// val rbt (a:Type) : Type
// instance val rbt_son_container0 (a:eqtype)
//   : container0 a (rbt a)
