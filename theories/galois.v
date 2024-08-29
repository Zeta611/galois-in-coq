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

  Parameter join : t → t → option t.
  Notation "x '⊔' y" := (join x y) (at level 50).
  Axiom join_order : ∀ x y j, x ⊔ y = Some j → x ⊑ j ∧ y ⊑ j.
  Axiom join_lub : ∀ x y z j, x ⊔ y = Some j → x ⊑ z → y ⊑ z → j ⊑ z.

  Parameter meet : t → t → option t.
  Notation "x '⊓' y" := (meet x y) (at level 40).
  Axiom meet_order : ∀ x y m, x ⊓ y = Some m → m ⊑ x ∧ m ⊑ y.
  Axiom meet_glb : ∀ x y z m, x ⊓ y = Some m → z ⊑ x → z ⊑ y → z ⊑ m.
End Poset.

Module Type Galois (𝒞 : Poset) (𝒜 : Poset).
  Parameter α : 𝒞.t → 𝒜.t.
  Parameter γ : 𝒜.t → 𝒞.t.

  Local Notation "x '⊑' y" := (𝒞.order x y) (at level 70).
  Local Notation "x '≼' y" := (𝒜.order x y) (at level 70).
  Local Notation "x '⊔' y" := (𝒞.join x y) (at level 50).
  Local Notation "x '⋎' y" := (𝒜.join x y) (at level 50).
  Local Notation "x '⊓' y" := (𝒞.meet x y) (at level 40).
  Local Notation "x '⋏' y" := (𝒜.meet x y) (at level 40).

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

  Lemma α_preserves_join : ∀ x y j j',
    x ⊔ y = Some j → α x ⋎ α y = Some j' → 𝒜.eq (α j) j'.
  Proof.
    intros x y j j' Hjoin_C Hjoin_A.
    apply 𝒜.order_antisym.
    - apply 𝒜.join_order in Hjoin_A.
      destruct Hjoin_A.
      repeat match goal with
      | H : _ ≼ _ |- _ => apply connection in H
      end.
      eapply 𝒞.join_lub in Hjoin_C; eauto.
      apply connection. assumption.
    - apply 𝒞.join_order in Hjoin_C.
      eapply 𝒜.join_lub;
        try eapply α_monotone; eauto; firstorder.
  Qed.

  Lemma γ_preserves_meet : ∀ x' y' m' m,
    x' ⋏ y' = Some m' → γ x' ⊓ γ y' = Some m → 𝒞.eq (γ m') m.
  Proof.
    intros x' y' m' m Hmeet_A Hmeet_C.
    apply 𝒞.order_antisym.
    - apply 𝒜.meet_order in Hmeet_A.
      eapply 𝒞.meet_glb in Hmeet_C;
        try eapply γ_monotone; eauto; firstorder.
    - apply 𝒞.meet_order in Hmeet_C.
      destruct Hmeet_C.
      repeat match goal with
      | H : _ ⊑ _ |- _ => apply connection in H
      end.
      eapply 𝒜.meet_glb in Hmeet_A; eauto.
      apply connection. assumption.
  Qed.
End Galois.
