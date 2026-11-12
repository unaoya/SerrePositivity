module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveBottomCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveLeftProper
public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitFromBottom
public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousHomotopyColimit

/-! # Actual hocolim comparisons without cofibrancy of the initial value

A relative projective cofibration from the constant initial-value diagram
suffices in a left proper model category. The proof changes the base of
the actual projective replacement, then uses Ken Brown in an under category.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.HomotopyColimit
variable {K : Type w} [PartialOrder K] [OrderBot K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

lemma comparison_weakEquivalence_of_fromBottom (D : K ⥤ C)
    (hD : let := Projective.modelCategory K I J;
      cofibrations (K ⥤ C) (ContinuousLifts.fromBottom D)) :
    weakEquivalences C ((comparison K I J).app D) := by
  let := Projective.modelCategory K I J
  have := Projective.leftProper K I J
  have := Projective.colimit_isLeftQuillen K I J
  let R := (replacement K I J).obj D
  let r := (replacementComparison K I J).app D
  let A := (Functor.const K).obj (D.obj ⊥)
  let B := (Functor.const K).obj (R.obj ⊥)
  let i : B ⟶ R := ContinuousLifts.fromBottom R
  let j : B ⟶ A := (Functor.const K).map (r.app ⊥)
  have hi : cofibrations (K ⥤ C) i :=
    Projective.fromBottom_cofibration_of_isCofibrant I J R (replacement_isCofibrant K I J D)
  have hj : weakEquivalences (K ⥤ C) j := fun _ =>
    replacementComparison_objectwiseWeakEquivalence K I J D ⊥
  let P := pushout i j
  let u : R ⟶ P := pushout.inl i j
  let v : A ⟶ P := pushout.inr i j
  let t : P ⟶ D := pushout.desc r (ContinuousLifts.fromBottom D)
    (ContinuousLifts.fromBottom_naturality r)
  have hu : weakEquivalences (K ⥤ C) u :=
    Quillen.weakEquivalence_of_pushout_along_cofibration (IsPushout.of_hasPushout i j) hi hj
  have hv : cofibrations (K ⥤ C) v :=
    (cofibrations (K ⥤ C)).of_isPushout (IsPushout.of_hasPushout i j).flip hi
  have hr : weakEquivalences (K ⥤ C) r :=
    replacementComparison_objectwiseWeakEquivalence K I J D
  have hut : u ≫ t = r := pushout.inl_desc _ _ _
  have ht : weakEquivalences (K ⥤ C) t :=
    (weakEquivalences (K ⥤ C)).of_precomp _ _ hu (hut.symm ▸ hr)
  let m : Under.mk v ⟶ Under.mk (ContinuousLifts.fromBottom D) :=
    Under.homMk t (pushout.inr_desc _ _ _)
  have : IsCofibrant (Under.mk v) := (UnderModel.isCofibrant_iff _).mpr ⟨hv⟩
  have : IsCofibrant (Under.mk (ContinuousLifts.fromBottom D)) :=
    (UnderModel.isCofibrant_iff _).mpr ⟨hD⟩
  have : WeakEquivalence m := ⟨ht⟩
  let F := Under.forget A ⋙ (colim : (K ⥤ C) ⥤ C)
  have hm := Quillen.map_weakEquivalence_of_cofibrant F m
  have hct : weakEquivalences C ((colim : (K ⥤ C) ⥤ C).map t) := mem_weakEquivalences (F.map m)
  have : Cofibration i := ⟨hi⟩
  have hci : cofibrations C ((colim : (K ⥤ C) ⥤ C).map i) :=
    (cofibration_iff _).mp (Quillen.map_cofibration (colim : (K ⥤ C) ⥤ C) i)
  have hcj : weakEquivalences C ((colim : (K ⥤ C) ⥤ C).map j) :=
    ColimitFromBottom.weakEquivalence_const_map K (r.app ⊥)
      (replacementComparison_objectwiseWeakEquivalence K I J D ⊥)
  have hcu : weakEquivalences C ((colim : (K ⥤ C) ⥤ C).map u) :=
    Quillen.weakEquivalence_of_pushout_along_cofibration
      ((IsPushout.of_hasPushout i j).map (colim : (K ⥤ C) ⥤ C)) hci hcj
  change weakEquivalences C ((colim : (K ⥤ C) ⥤ C).map r)
  have he : (colim : (K ⥤ C) ⥤ C).map u ≫ (colim : (K ⥤ C) ⥤ C).map t =
      (colim : (K ⥤ C) ⥤ C).map r :=
    ((colim : (K ⥤ C) ⥤ C).map_comp u t).symm.trans
      (congrArg (colim : (K ⥤ C) ⥤ C).map hut)
  exact he ▸ (weakEquivalences C).comp_mem _ _ hcu hct

lemma comparison_weakEquivalence_const (X : C) :
    weakEquivalences C ((comparison K I J).app ((Functor.const K).obj X)) := by
  let := Projective.modelCategory K I J
  have (k : K) : IsIso ((ContinuousLifts.fromBottom ((Functor.const K).obj X)).app k) :=
    inferInstanceAs (IsIso (𝟙 X))
  have : IsIso (ContinuousLifts.fromBottom ((Functor.const K).obj X)) :=
    NatIso.isIso_of_isIso_app _
  exact comparison_weakEquivalence_of_fromBottom I J _
    ((cofibrations (K ⥤ C)).of_isIso _)

end SerrePositivity.DiagramModel.HomotopyColimit

namespace SerrePositivity.DiagramModel.HomotopyColimit
variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

/-- Every continuous cofibration sequence computes its actual hocolim,
with no cofibrancy requirement on the initial object. -/
lemma comparison_weakEquivalence_of_continuous_leftProper (D : K ⥤ C)
    [D.IsWellOrderContinuous]
    (hstep : ∀ (k : K), ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    weakEquivalences C ((comparison K I J).app D) :=
  comparison_weakEquivalence_of_fromBottom I J D (Projective.fromBottom_cofibration I J D hstep)

end SerrePositivity.DiagramModel.HomotopyColimit
