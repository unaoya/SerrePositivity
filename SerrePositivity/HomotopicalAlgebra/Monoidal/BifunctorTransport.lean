module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor

/-! # Transport and parameter restriction of Quillen bifunctors -/

@[expose] public section
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.Quillen
variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {D : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} D]
  [ModelCategory C₁] [ModelCategory C₂] [ModelCategory C₃] [ModelCategory D]
  {F F' : C₁ ⥤ C₂ ⥤ C₃}

/-- Natural comparisons preserve the full pushout-product condition. -/
lemma isQuillenBifunctor_of_natIso (e : F ≅ F') [IsQuillenBifunctor F] :
    IsQuillenBifunctor F' := by
  constructor
  · intro A B X Y i j sq hi hj
    have hc := IsQuillenBifunctor.cofibration i j (sq.ofNatIso e.symm) hi hj
    let iso : Arrow.mk (sq.ofNatIso e.symm).ι ≅ Arrow.mk sq.ι :=
      Arrow.isoMk (Iso.refl _) ((e.app B).app Y) (by
        dsimp [Functor.PushoutObjObj.ofNatIso]
        simp [Category.assoc, ← NatTrans.comp_app])
    exact (cofibration_iff _).2
      (((cofibrations C₃).arrow_mk_iso_iff iso).1 ((cofibration_iff _).1 hc))
  · intro A B X Y i j sq hi hj hw
    have hc := IsQuillenBifunctor.weakEquivalence i j (sq.ofNatIso e.symm) hi hj hw
    let iso : Arrow.mk (sq.ofNatIso e.symm).ι ≅ Arrow.mk sq.ι :=
      Arrow.isoMk (Iso.refl _) ((e.app B).app Y) (by
        dsimp [Functor.PushoutObjObj.ofNatIso]
        simp [Category.assoc, ← NatTrans.comp_app])
    exact (weakEquivalence_iff _).2
      (((weakEquivalences C₃).arrow_mk_iso_iff iso).1 ((weakEquivalence_iff _).1 hc))

/-- Restricting the first variable along a left Quillen functor preserves
the two-variable condition, including its trivial-input cases. -/
lemma isQuillenBifunctor_restrict (L : D ⥤ C₁) [IsLeftQuillen L] [IsQuillenBifunctor F] :
    IsQuillenBifunctor (L ⋙ F) := by
  have hC {A B : D} (i : A ⟶ B) (hi : Cofibration i) : Cofibration (L.map i) :=
    (cofibration_iff _).2 (IsLeftQuillen.map_cofibrations i ((cofibration_iff _).1 hi))
  constructor
  · intro A B X Y i j sq hi hj
    let s : F.PushoutObjObj (L.map i) j :=
      { pt := sq.pt, inl := sq.inl, inr := sq.inr, isPushout := sq.isPushout,
        ι := sq.ι, inl_ι := sq.inl_ι, inr_ι := sq.inr_ι }
    exact IsQuillenBifunctor.cofibration (F := F) (L.map i) j s (hC i hi) hj
  · intro A B X Y i j sq hi hj hw
    let s : F.PushoutObjObj (L.map i) j :=
      { pt := sq.pt, inl := sq.inl, inr := sq.inr, isPushout := sq.isPushout,
        ι := sq.ι, inl_ι := sq.inl_ι, inr_ι := sq.inr_ι }
    apply IsQuillenBifunctor.weakEquivalence (F := F) (L.map i) j s (hC i hi) hj
    rcases hw with hiw | hjw
    · exact Or.inl ((weakEquivalence_iff _).2
        (IsLeftQuillen.map_trivialCofibrations i
          ((mem_trivialCofibrations_iff _).2 ⟨hi, hiw⟩)).2)
    · exact Or.inr hjw

end SerrePositivity.Quillen
