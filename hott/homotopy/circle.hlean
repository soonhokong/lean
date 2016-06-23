/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the circle
-/

import .sphere
import types.int.hott
import algebra.homotopy_group .connectedness

open eq susp bool sphere_index is_equiv equiv is_trunc is_conn pi algebra

definition circle : Type₀ := sphere 1

namespace circle
  notation `S¹` := circle
  definition base1 : S¹ := !north
  definition base2 : S¹ := !south
  definition seg1 : base1 = base2 := merid !north
  definition seg2 : base1 = base2 := merid !south

  definition base : S¹ := base1
  definition loop : base = base := seg2 ⬝ seg1⁻¹

  definition rec2 {P : S¹ → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2) (x : S¹) : P x :=
  begin
    induction x with b,
    { exact Pb1},
    { exact Pb2},
    { esimp at *, induction b with y,
      { exact Ps1},
      { exact Ps2},
      { cases y}},
  end

  definition rec2_on [reducible] {P : S¹ → Type} (x : S¹) (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2) : P x :=
  circle.rec2 Pb1 Pb2 Ps1 Ps2 x

  theorem rec2_seg1 {P : S¹ → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  !rec_merid

  theorem rec2_seg2 {P : S¹ → Type} (Pb1 : P base1) (Pb2 : P base2)
    (Ps1 : Pb1 =[seg1] Pb2) (Ps2 : Pb1 =[seg2] Pb2)
      : apd (rec2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  !rec_merid

  definition elim2 {P : Type} (Pb1 Pb2 : P) (Ps1 Ps2 : Pb1 = Pb2) (x : S¹) : P :=
  rec2 Pb1 Pb2 (pathover_of_eq _ Ps1) (pathover_of_eq _ Ps2) x

  definition elim2_on [reducible] {P : Type} (x : S¹) (Pb1 Pb2 : P)
    (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2) : P :=
  elim2 Pb1 Pb2 Ps1 Ps2 x

  theorem elim2_seg1 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg1),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim2,rec2_seg1],
  end

  theorem elim2_seg2 {P : Type} (Pb1 Pb2 : P) (Ps1 : Pb1 = Pb2) (Ps2 : Pb1 = Pb2)
    : ap (elim2 Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg2),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim2,rec2_seg2],
  end

  definition elim2_type (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2) (x : S¹) : Type :=
  elim2 Pb1 Pb2 (ua Ps1) (ua Ps2) x

  definition elim2_type_on [reducible] (x : S¹) (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2)
    : Type :=
  elim2_type Pb1 Pb2 Ps1 Ps2 x

  theorem elim2_type_seg1 (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2)
    : transport (elim2_type Pb1 Pb2 Ps1 Ps2) seg1 = Ps1 :=
  by rewrite [tr_eq_cast_ap_fn,↑elim2_type,elim2_seg1];apply cast_ua_fn

  theorem elim2_type_seg2 (Pb1 Pb2 : Type) (Ps1 Ps2 : Pb1 ≃ Pb2)
    : transport (elim2_type Pb1 Pb2 Ps1 Ps2) seg2 = Ps2 :=
  by rewrite [tr_eq_cast_ap_fn,↑elim2_type,elim2_seg2];apply cast_ua_fn

  protected definition rec {P : S¹ → Type} (Pbase : P base) (Ploop : Pbase =[loop] Pbase)
    (x : S¹) : P x :=
  begin
    fapply (rec2_on x),
    { exact Pbase},
    { exact (transport P seg1 Pbase)},
    { apply pathover_tr},
    { apply pathover_tr_of_pathover, exact Ploop}
  end

  protected definition rec_on [reducible] {P : S¹ → Type} (x : S¹) (Pbase : P base)
    (Ploop : Pbase =[loop] Pbase) : P x :=
  circle.rec Pbase Ploop x

  theorem rec_loop_helper {A : Type} (P : A → Type)
    {x y z : A} {p : x = y} {p' : z = y} {u : P x} {v : P z} (q : u =[p ⬝ p'⁻¹] v) :
    pathover_tr_of_pathover q ⬝o !pathover_tr⁻¹ᵒ = q :=
  by cases p'; cases q; exact idp

  definition con_refl {A : Type} {x y : A} (p : x = y) : p ⬝ refl _ = p :=
  eq.rec_on p idp

  theorem rec_loop {P : S¹ → Type} (Pbase : P base) (Ploop : Pbase =[loop] Pbase) :
    apd (circle.rec Pbase Ploop) loop = Ploop :=
  begin
    rewrite [↑loop,apd_con,↑circle.rec,↑circle.rec2_on,↑base,rec2_seg2,apd_inv,rec2_seg1],
    apply rec_loop_helper
  end

  protected definition elim {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    (x : S¹) : P :=
  circle.rec Pbase (pathover_of_eq _ Ploop) x

  protected definition elim_on [reducible] {P : Type} (x : S¹) (Pbase : P)
    (Ploop : Pbase = Pbase) : P :=
  circle.elim Pbase Ploop x

  theorem elim_loop {P : Type} (Pbase : P) (Ploop : Pbase = Pbase) :
    ap (circle.elim Pbase Ploop) loop = Ploop :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant loop),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑circle.elim,rec_loop],
  end

  theorem elim_seg1 {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    : ap (circle.elim Pbase Ploop) seg1 = (tr_constant seg1 Pbase)⁻¹ :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg1),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑circle.elim,↑circle.rec],
    rewrite [↑circle.rec2_on,rec2_seg1], apply inverse,
    apply pathover_of_eq_tr_constant_inv
  end

  theorem elim_seg2 {P : Type} (Pbase : P) (Ploop : Pbase = Pbase)
    : ap (circle.elim Pbase Ploop) seg2 = Ploop ⬝ (tr_constant seg1 Pbase)⁻¹ :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg2),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑circle.elim,↑circle.rec],
    rewrite [↑circle.rec2_on,rec2_seg2],
    assert l : Π(A B : Type)(a a₂ a₂' : A)(b b' : B)(p : a = a₂)(p' : a₂' = a₂)
                   (q : b = b'),
             pathover_tr_of_pathover (pathover_of_eq _ q)
           = pathover_of_eq _ (q ⬝ (tr_constant p' b')⁻¹)
           :> b =[p] p' ▸ b',
    { intros, cases q, cases p', cases p, reflexivity },
    apply l
  end

  protected definition elim_type (Pbase : Type) (Ploop : Pbase ≃ Pbase)
    (x : S¹) : Type :=
  circle.elim Pbase (ua Ploop) x

  protected definition elim_type_on [reducible] (x : S¹) (Pbase : Type)
    (Ploop : Pbase ≃ Pbase) : Type :=
  circle.elim_type Pbase Ploop x

  theorem elim_type_loop (Pbase : Type) (Ploop : Pbase ≃ Pbase) :
    transport (circle.elim_type Pbase Ploop) loop = Ploop :=
  by rewrite [tr_eq_cast_ap_fn,↑circle.elim_type,elim_loop];apply cast_ua_fn

  theorem elim_type_loop_inv (Pbase : Type) (Ploop : Pbase ≃ Pbase) :
    transport (circle.elim_type Pbase Ploop) loop⁻¹ = to_inv Ploop :=
  by rewrite [tr_inv_fn]; apply inv_eq_inv; apply elim_type_loop
end circle

attribute circle.base1 circle.base2 circle.base [constructor]
attribute circle.rec2 circle.elim2 [unfold 6] [recursor 6]
attribute circle.elim2_type [unfold 5]
attribute circle.rec2_on circle.elim2_on [unfold 2]
attribute circle.elim2_type [unfold 1]
attribute circle.rec circle.elim [unfold 4] [recursor 4]
attribute circle.elim_type [unfold 3]
attribute circle.rec_on circle.elim_on [unfold 2]
attribute circle.elim_type_on [unfold 1]

namespace circle
  open sigma
  /- universal property of the circle -/
  definition circle_pi_equiv [constructor] (P : S¹ → Type)
    : (Π(x : S¹), P x) ≃ Σ(p : P base), p =[loop] p :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨f base, apd f loop⟩},
    { intro v x, induction v with p q, induction x,
      { exact p},
      { exact q}},
    { intro v, induction v with p q, fapply sigma_eq,
      { reflexivity},
      { esimp, apply pathover_idp_of_eq, apply rec_loop}},
    { intro f, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover_dep, apply hdeg_squareover, esimp, apply rec_loop}}
  end

  definition circle_arrow_equiv [constructor] (P : Type)
    : (S¹ → P) ≃ Σ(p : P), p = p :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨f base, ap f loop⟩},
    { intro v x, induction v with p q, induction x,
      { exact p},
      { exact q}},
    { intro v, induction v with p q, fapply sigma_eq,
      { reflexivity},
      { esimp, apply pathover_idp_of_eq, apply elim_loop}},
    { intro f, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover, apply hdeg_square, esimp, apply elim_loop}}
  end

  definition pointed_circle [instance] [constructor] : pointed S¹ :=
  pointed.mk base

  definition pcircle [constructor] : Type* := pointed.mk' S¹
  notation `S¹.` := pcircle

  definition loop_neq_idp : loop ≠ idp :=
  assume H : loop = idp,
  have H2 : Π{A : Type₁} {a : A} {p : a = a}, p = idp,
    from λA a p, calc
      p   = ap (circle.elim a p) loop : elim_loop
      ... = ap (circle.elim a p) (refl base) : by rewrite H,
  eq_bnot_ne_idp H2

  definition circle_turn [reducible] (x : S¹) : x = x :=
  begin
    induction x,
    { exact loop },
    { apply eq_pathover, apply square_of_eq, rewrite ap_id }
  end

  definition turn_neq_idp : circle_turn ≠ (λx, idp) :=
  assume H : circle_turn = λx, idp,
  have H2 : loop = idp, from apd10 H base,
  absurd H2 loop_neq_idp

  open int

  protected definition code [unfold 1] (x : S¹) : Type₀ :=
  circle.elim_type_on x ℤ equiv_succ

  definition transport_code_loop (a : ℤ) : transport circle.code loop a = succ a :=
  ap10 !elim_type_loop a

  definition transport_code_loop_inv (a : ℤ) : transport circle.code loop⁻¹ a = pred a :=
  ap10 !elim_type_loop_inv a

  protected definition encode [unfold 2] {x : S¹} (p : base = x) : circle.code x :=
  transport circle.code p (0 : ℤ)

  protected definition decode [unfold 1] {x : S¹} : circle.code x → base = x :=
  begin
    induction x,
    { exact power loop},
    { apply arrow_pathover_left, intro b, apply eq_pathover_constant_left_id_right,
      apply square_of_eq, rewrite [idp_con, power_con,transport_code_loop]}
  end

  definition circle_eq_equiv [constructor] (x : S¹) : (base = x) ≃ circle.code x :=
  begin
    fapply equiv.MK,
    { exact circle.encode},
    { exact circle.decode},
    { exact abstract [irreducible] begin
      induction x,
      { intro a, esimp, apply rec_nat_on a,
        { exact idp},
        { intros n p, rewrite [↑circle.encode, -power_con, con_tr, transport_code_loop],
          exact ap succ p},
        { intros n p, rewrite [↑circle.encode, nat_succ_eq_int_succ, neg_succ, -power_con_inv,
            @con_tr _ circle.code, transport_code_loop_inv, ↑[circle.encode] at p, p, -neg_succ] }},
      { apply pathover_of_tr_eq, apply eq_of_homotopy, intro a, apply @is_set.elim,
        esimp, exact _} end end},
    { intro p, cases p, exact idp},
  end

  definition base_eq_base_equiv [constructor] : base = base ≃ ℤ :=
  circle_eq_equiv base

  definition decode_add (a b : ℤ) : circle.decode (a +[ℤ] b) = circle.decode a ⬝ circle.decode b :=
  !power_con_power⁻¹

  definition encode_con (p q : base = base)
    : circle.encode (p ⬝ q) = circle.encode p +[ℤ] circle.encode q :=
  preserve_binary_of_inv_preserve base_eq_base_equiv concat (@add ℤ _) decode_add p q

  --the carrier of π₁(S¹) is the set-truncation of base = base.
  open algebra trunc group

  definition fg_carrier_equiv_int : π[1](S¹.) ≃ ℤ :=
  trunc_equiv_trunc 0 base_eq_base_equiv ⬝e @(trunc_equiv 0 ℤ) proof _ qed

  definition con_comm_base (p q : base = base) : p ⬝ q = q ⬝ p :=
  eq_of_fn_eq_fn base_eq_base_equiv (by esimp;rewrite [+encode_con,add.comm])

  definition fundamental_group_of_circle : π₁(S¹.) ≃g gℤ :=
  begin
    apply (isomorphism_of_equiv fg_carrier_equiv_int),
    intros g h,
    induction g with g', induction h with h',
    apply encode_con,
  end

  open nat
  definition homotopy_group_of_circle (n : ℕ) : πg[n+1 +1] S¹. ≃g G0 :=
  begin
    refine @trivial_homotopy_add_of_is_set_loop_space S¹. 1 n _,
    apply is_trunc_equiv_closed_rev, apply base_eq_base_equiv
  end

  definition eq_equiv_Z (x : S¹) : x = x ≃ ℤ :=
  begin
    induction x,
    { apply base_eq_base_equiv},
    { apply equiv_pathover, intro p p' q, apply pathover_of_eq,
      note H := eq_of_square (square_of_pathover q),
      rewrite con_comm_base at H,
      note H' := cancel_left _ H,
      induction H', reflexivity}
  end

  proposition is_trunc_circle [instance] : is_trunc 1 S¹ :=
  begin
    apply is_trunc_succ_of_is_trunc_loop,
    { apply trunc_index.minus_one_le_succ},
    { intro x, apply is_trunc_equiv_closed_rev, apply eq_equiv_Z}
  end

  proposition is_conn_circle [instance] : is_conn 0 S¹ :=
  sphere.is_conn_sphere -1.+2

  definition circle_mul [reducible] (x y : S¹) : S¹ :=
  circle.elim y (circle_turn y) x

  definition circle_mul_base (x : S¹) : circle_mul x base = x :=
  begin
    induction x,
    { reflexivity },
    { apply eq_pathover_id_right, apply hdeg_square, apply elim_loop }
  end

  definition circle_base_mul [reducible] (x : S¹) : circle_mul base x = x :=
  idp

end circle
