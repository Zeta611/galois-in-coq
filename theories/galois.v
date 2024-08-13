From stdpp Require Import base.

Module Type Poset.
  Parameter t : Type.
  Parameter eq : t → t → Prop.
  Notation "x '==' y" := (eq x y) (at level 70).
  Axiom eq_refl : ∀ x, x == x.
  Axiom eq_sym : ∀ x y, x == y → y == x.
  Axiom eq_trans : ∀ x y z, x == y → y == z → x == z.

  Parameter order : t → t → Prop.
  Notation "x '⊑' y" := (order x y) (at level 70).
  Axiom order_refl : ∀ x y, x == y → x ⊑ y.
  Axiom order_antisym: ∀ x y, x ⊑ y → y ⊑ x → x == y.
  Axiom order_trans : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z.
End Poset.

Module Type Galois (𝒞 : Poset) (𝒜 : Poset).
  Parameter α : 𝒞.t → 𝒜.t.
  Parameter γ : 𝒜.t → 𝒞.t.

  Local Notation "x '≼' y" := (𝒜.order x y) (at level 70).
  Local Notation "x '⊑' y" := (𝒞.order x y) (at level 70).

  Axiom connection : ∀ (x : 𝒞.t) (x' : 𝒜.t),
    (α x) ≼ x' ↔ x ⊑ (γ x').

  Lemma γα_inflationary : ∀ x, x ⊑ γ (α x).
  Proof.
    intros.
    apply connection.
    apply 𝒜.order_refl.
    apply 𝒜.eq_refl.
  Qed.

  Lemma αγ_deflationary : ∀ x', α (γ x') ≼ x'.
  Proof.
    intros.
    apply connection.
    apply 𝒞.order_refl.
    apply 𝒞.eq_refl.
  Qed.

  Lemma γ_monotone : ∀ x' y', x' ≼ y' → (γ x') ⊑ (γ y').
  Proof.
    intros.
    apply connection.
    apply 𝒜.order_trans with (y := x'); auto.
    apply αγ_deflationary.
  Qed.

  Lemma α_monotone : ∀ x y, x ⊑ y → (α x) ≼ (α y).
  Proof.
    intros.
    apply connection.
    apply 𝒞.order_trans with (y := y); auto.
    apply γα_inflationary.
  Qed.
End Galois.
