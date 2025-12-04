module Clase11.Calc

(* Algoritmo extendido de Euclides *)

open FStar.Mul

(* [a] divide a [b] *)
let ( /? ) a b = exists (c:int). a * c == b

let intro_divides (a b : int) (c : int)
  : Lemma (requires a * c == b)
          (ensures a /? b)
  = ()

  // gcd 8 18 = 2
  // a*8 + b*18 = 2
  // (-2)*8 + 1*18 = 2

let elim_divides (a b : int)
  : Ghost int
      (requires a /? b)
      (ensures fun c -> a * c == b)
  = FStar.IndefiniteDescription.indefinite_description_ghost _ (fun c -> a * c == b)

let is_cd (x y : int) (z : int) = z /? x /\ z /? y

let is_gcd (x y : int) (z : int) =
  is_cd x y z /\ (forall z'. z' > z ==> ~ (is_cd x y z'))

let div_neg (x y : int)
: Lemma (requires x /? y)
        (ensures  x /? (-y))
        [SMTPat (x /? (-y))]
=
  let c = elim_divides x y in
  intro_divides x (-y) (-c)

let mayor_no_div (x:pos) (z:int)
: Lemma (requires z > x /\ z /? x)
        (ensures False)
=
  ()

let lem_gcd_0 (x:pos) : Lemma (is_gcd x 0 x) =
  assert (1 * x == x);
  assert (x /? x);
  assert (x /? 0);
  assert (is_cd x 0 x);
  ()

let lem_gcd_sym (x y g : int)
: Lemma (is_gcd x y g <==> is_gcd y x g)
= ()

let div_add (x y z : int)
: Lemma (requires z /? x /\ z /? y)
        (ensures z /? (x+y))
=
  let c1 = elim_divides z x in
  let c2 = elim_divides z y in
  intro_divides z (x + y) (c1 + c2)

let div_sub (x y z : int)
: Lemma (requires z /? x /\ z /? y)
        (ensures z /? (x-y))
=
  div_add x (-y) z

let lem_gcd_add (x y g : int)
: Lemma (is_gcd x y g <==> is_gcd x (x+y) g)
=
  let aux (z:int) : Lemma (is_cd x y z <==> is_cd x (x+y) z) =
    calc (<==>) {
        is_cd x y z;
        <==> {}
        z /? x /\ z /? y;
        <==> { Classical.move_requires (div_add x y) z;
               Classical.move_requires (div_sub (x+y) x) z }
        z /? x /\ z /? (x+y);
        <==> {}
        is_cd x (x+y) z;
    }
  in
  Classical.forall_intro aux;
  ()

let lem_gcd_sub (x y g : int)
: Lemma (ensures is_gcd x y g <==> is_gcd (x-y) y g)
=
  calc (<==>) {
    is_gcd x y g;
    <==> {}
    is_gcd y x g;
    <==> { lem_gcd_add y (x-y) g }
    is_gcd y (x-y) g;
    <==> {}
    is_gcd (x-y) y g;
  }

let rec lem_gcd_mod (x y g : nat)
: Lemma (requires y <> 0)
        (ensures is_gcd x y g <==> is_gcd (x%y) y g)
=
  if x < y then (
    calc (<==>) {
      is_gcd x y g;
      <==> { Math.Lemmas.small_mod x y; assert (x%y == x) }
      is_gcd (x%y) y g;
    }
  ) else (
    calc (<==>) {
      is_gcd x y g;
      <==> { lem_gcd_sub x y g }
      is_gcd (x-y) y g;
      <==> { lem_gcd_mod (x-y) y g }
      is_gcd ((x-y) % y) y g;
      <==> {
        Math.Lemmas.sub_div_mod_1 x y;
        assert ((x-y)%y == x%y)
      }
      is_gcd (x%y) y g;
    }
  )

let gcd_of (x y : nat) : Type =
  (a:int & b:int & g:nat{a*x + b*y == g /\ is_gcd x y g})

let rec egcd (x y : nat)
: Pure (gcd_of x y)
       (requires x <> 0 \/ y <> 0)
       (ensures fun _ -> True)
       (decreases y)
=
  if x = 0 then (
    lem_gcd_0 y;
    (| 0, 1, y |)
  ) else if y = 0 then (
    lem_gcd_0 x;
    (| 1, 0, x |)
  ) else if x < y then (
    let (| a, b, g |) = egcd y x in
    (| b, a, g |)
  ) else (
    let (| a, b, g |) = egcd y (x%y) in
    assert (a*y + b*(x%y) == g);
    let r = x/y in
    assert (is_gcd y (x%y) g);
    assert (y <> 0);

    calc (==) {
      b*x + (a-b*r)*y;
      == {}
      b*x + (a-b*(x/y))*y;
      == { Math.Lemmas.distributivity_sub_left a (b*(x/y)) y }
      b*x + a*y - b*(x/y)*y;
      == { Math.Lemmas.paren_mul_right b (x/y) y }
      b*x + a*y - b*((x/y)*y);
      == { Math.Lemmas.distributivity_sub_right b x ((x/y)*y) }
      a*y + b * (x - (x/y)*y);
      == { Math.Lemmas.euclidean_division_definition x y }
      a*y + b * (x%y);
      == { () }
      g;
    };

    lem_gcd_mod x y g;
    assert (is_gcd x y g);
    (| b, a-b*(x/y), g |)
  )
