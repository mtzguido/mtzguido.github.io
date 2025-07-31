module Tuto

module B = LowStar.Buffer
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module S = FStar.Seq
module L = C.Loops

open FStar.HyperStack.ST

// LOW* TUTORIAL

// This is a shallow embedding, so any concept from C is "encoded" as an F* concept.
// For instance: machine integers. We cannot compile nat to C! (Why?) So we model machine integers.
let x: U32.t = 0ul

let _ = assert (U32.v x == 0)

// Actually, this is just syntactic sugar for
let x_real = FStar.UInt32.uint_to_t 0

// Such a model has to avoid some issues:
// - extraction: this must appear as a distinct type
// type uint32 = x:nat { x <= 0xffffffff } // this would NOT work!!!
// - soundness: we cannot over-define this type (e.g. shifts in C)
let x_shifted = admit (); x_real `U32.shift_left` 32ul

// Other pleasant things: overflow for signed integers, and many more...

// Let's talk about extraction a little bit. Extraction ERASES proofs and
// refinements; so we must ensure that each of the machine integers remains a
// distinct type. Extraction normally goes like this:
// F* --> erased AST ("ML" AST) --> OCaml pretty-printing

// Now we switch to:
// Low* (subset) --> erased AST ("ML" AST) --> karamel (dedicated compiler) --> C

// How to talk about memory? We define a new effect that has a *state*, that models the C stack and heap.
// Consider the ST effect.
let f (): ST unit (requires fun h0 -> True) (ensures fun h0 r h1 -> True) =
  let r = B.malloc HS.root 0ul 16ul in
  // How to reason about the state of the memory? Just like machine integers are
  // reflect as nats, memory is reflected as a map.
  let h: HS.mem = ST.get () in
  // A pointer is an address, and the map associates to each address as sequence
  // of values (CompCert-like memory model).
  let r_as_pure_sequence: Ghost.erased _ = B.as_seq h r in
  // Sequences are pure arrays meant to provide index-based reasoning
  assert (S.index r_as_pure_sequence 8 == 0ul);
  // An equational theory of sequences tells us that the post-condition of `upd` changes `r` (how?)
  B.upd r 0ul 1ul;
  // The lemmas that characterize upd, index, and create (see FStar.Seq) allow the SMT to conclude these facts.
  let h1: HS.mem = ST.get () in
  assert (S.index (B.as_seq h1 r) 8 == 0ul);
  assert (S.index (B.as_seq h1 r) 0 == 1ul);
  ()

// Another key consideration is liveness of values, and modifications
let incr (r: B.buffer U32.t) (other: B.buffer U32.t):
  Stack unit
    (requires fun h0 -> B.live h0 r /\ B.live h0 other)
    (ensures (fun h0 _ h1 -> B.(modifies (loc_buffer r) h0 h1)))
=
  admit ();
  // Something missing here...
  let r_v = B.index r 0ul in
  B.upd r 0ul (r_v `U32.add_mod` 1ul)

// Modeling the stack is done through a series of "frames" that need to be
// manually pushed and popped (bad design -- would not do again!).
let call_incr (): Stack unit
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
=
  push_frame ();
  let r = B.alloca 0ul 1ul in
  let other = B.alloca 0ul 8ul in
  let h0 = ST.get () in
  incr r other;
  let h1 = ST.get () in
  admit ();
  // Something missing here...
  assert (B.get h1 r 0 == 1ul);
  // Note that the modifies-clauses theory (another equational theory, like
  // sequence, encoded to the SMT), describes the interaction of liveness
  // predicates and modification predicates. Notably, each address is assigned a
  // predicate that tracks its originating /region/ (heap, or a stack frame),
  // and this region allows reasoning about the stack.
  assert (B.as_seq h1 other `S.equal` B.as_seq h0 other);
  // Let's inspect push_frame and pop_frame.
  pop_frame ()

// Finally, more dedicate constructs exist: operations on buffers (memcpy,
// memset), printf-style printers, endianness helpers, different flavors of
// buffers (immutable, frozen, "const" pointers), and on top of those are built
// data structures, such as resizable vectors, linked lists, maps, etc.

// COMPLETE EXAMPLE

let rec sum (s: S.seq U32.t): Ghost nat
  (requires True)
  (ensures fun _ -> True)
  (decreases S.length s)
=
  if S.eq s S.empty then
    0
  else
    U32.v (S.head s) + sum (S.tail s)

// How do these proofs work? Unrolling definitions in the SMT
let sum_zero (s: S.seq U32.t): Lemma (ensures (sum (S.slice s 0 0)) == 0) = ()

let sum_one (s: S.seq U32.t): Lemma (requires S.length s == 1) (ensures (sum s == U32.v (S.index s 0))) = ()

#set-options "--fuel 0 --ifuel 0"

// Explain in more detail: equational theory of sequences; infix operator notation; S.equal vs ==; etc.
// Why did I choose this particular lemma?
let rec sum_append (s1 s2: S.seq U32.t): Lemma (ensures (sum s1 + sum s2 == sum (s1 `S.append` s2))) (decreases (S.length s1)) =
  if S.eq s1 S.empty then
    calc (==) {
      sum (s1 `S.append` s2);
    (==) { S.append_empty_l s2 }
      sum s2;
    (==) { }
      0 + sum s2;
    (==) { normalize_term_spec (sum S.empty) }
      sum s1 + sum s2;
    }
  else if S.length s1 = 1 then
    // EXERCISE
    admit ()
  else
    let s1_hd = S.slice s1 0 1 in
    let s1_tl = S.slice s1 1 (S.length s1) in
    calc (==) {
      sum (s1 `S.append` s2);
    (==) { S.lemma_slice_append s1 s2 }
      sum S.(append s1_hd (append s1_tl s2));
    (==) { sum_append s1_hd (S.append s1_tl s2) }
      sum s1_hd + sum S.(append (slice s1 1 (length s1)) s2);
    (==) { sum_append s1_tl s2 }
      sum s1_hd + sum s1_tl + sum s2;
    (==) { sum_append s1_hd s1_tl }
      sum (S.append s1_hd s1_tl) + sum s2;
    (==) { S.lemma_split s1 1 }
      sum s1 + sum s2;
    }

let sum_overflow (s: S.seq U32.t) (i: nat): Lemma
  (requires (
    i < S.length s /\ (
    let s_up_to_i = S.slice s 0 i in
    sum s_up_to_i > FStar.UInt.max_int 32)))
  (ensures (
    let s_up_to_i1 = S.slice s 0 (i + 1) in
    sum s_up_to_i1 > FStar.UInt.max_int 32))
=
  S.lemma_split (S.slice s 0 (i + 1)) i;
  sum_append (S.slice s 0 i) (S.slice s i (i + 1))

val sum_low (b: B.buffer U32.t) (len: U32.t { len == B.len b }): Stack (option U32.t)
  (requires fun h0 ->
    B.live h0 b)
  (ensures fun h0 r h1 ->
    let s = B.as_seq h0 b in
    B.(modifies loc_none h0 h1) /\ (
    match r with
    | None -> sum s > FStar.UInt.max_int 32
    | Some r -> U32.v r = sum s))

let sum_low b len =
  let h0 = ST.get () in
  ST.push_frame ();
  let h1 = ST.get () in
  let r = B.alloca (Some 0ul) 1ul in
  let inv (h: HS.mem) (i: nat) =
    // Note that this is not "baked in". (Could be.)
    i <= U32.v len /\
    B.(modifies (loc_buffer r) h1 h) /\
    B.live h r /\ (
    let r = B.get h r 0 in
    let s = B.as_seq h0 b in
    let s_up_to_i = S.slice s 0 i in
    match r with
    | Some r ->
        U32.v r == sum s_up_to_i
    | None ->
        sum s_up_to_i > FStar.UInt.max_int 32)
  in
  sum_zero (B.as_seq h0 b);
  // Let's look at the signature of for.
  C.Loops.for 0ul len inv (fun i ->
    let r_v = B.index r 0ul in
    match r_v with
    | None ->
        sum_overflow (B.as_seq h0 b) (U32.v i)
    | Some r_v ->
        let b_i = B.index b i in
        // EXPLAIN
        let s = Ghost.hide (B.as_seq h0 b) in
        // Sanity check: invariant at index i, need to get invariant at index i+1.
        assert (U32.v r_v == sum (S.slice s 0 (U32.v i)));
        if i = 0ul then begin
          // SIMPLE CASE: first iteration, no overflow ever
          B.upd r 0ul (Some b_i);
          sum_one (S.slice s 0 (U32.v i + 1))
        end else
          let i = Ghost.hide (U32.v i) in
          calc (==) {
            sum (S.slice s 0 (i + 1));
          // == does not trigger the sequence reasoning; what would be a slightly better style?
          (==) { assert (S.equal (S.slice s 0 (i + 1)) (S.append (S.slice s 0 i) (S.slice s i (i + 1)))) }
            sum (S.append (S.slice s 0 i) (S.slice s i (i + 1)));
          (==) {sum_append (S.slice s 0 i) (S.slice s i (i + 1)) }
            sum (S.slice s 0 i) + sum (S.slice s i (i + 1));
          (==) {}
            U32.v r_v + sum (S.slice s i (i + 1));
          (==) { sum_one (S.slice s i (i + 1)) }
            U32.v r_v + U32.v b_i;
          };

          if r_v `U32.gt` (0xfffffffful `U32.sub` b_i) then
            // r_v + b_i > U32_MAX
            B.upd r 0ul None
          else
            B.upd r 0ul (Some (r_v `U32.add` b_i))
  );
  let h2 = ST.get () in
  // Why not dereference at the last minute?
  let r = B.index r 0ul in
  pop_frame ();
  let h3 = ST.get () in
  r

// EXERCISE: this is not very idiomatic C code! (Although any decent compiler will optimize it normally.)
// If you are a purist, rewrite this code in the following style (sketch):

val sum_low2 (dst: B.buffer U32.t { B.len dst == 1ul }) (b: B.buffer U32.t) (len: U32.t { len == B.len b }): Stack bool
  (requires fun h0 ->
    B.live h0 b /\ B.live h0 dst)
  (ensures fun h0 r h1 ->
    let s = B.as_seq h0 b in
    if r then
      (* overflowed *)
      sum s > FStar.UInt.max_int 32 /\ B.(modifies loc_none h0 h1)
    else
      U32.v (B.get h1 dst 0) == sum s /\ B.(modifies (loc_buffer dst) h0 h1))

let sum_low2 _ _ _ = admit ()
