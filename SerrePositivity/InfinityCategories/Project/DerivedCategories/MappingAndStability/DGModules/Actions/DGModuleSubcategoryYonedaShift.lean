module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorRestrictedYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorShiftIso
public import SerrePositivity.DifferentialGraded.Category.Tensor
/-!
概要：選んだ実加群部分圏の Yoneda と shift 同型。
方針：制限 Yoneda に同じ shift 比較を適用する。
規約：全同型コピーへの閉性を要求しない。
使われ方：代表系の前三角性に必要な実 shift の表現。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory MonoidalCategory DifferentialGraded

def dgClosedObjectsForget (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] :
    DGFunctor R (ClosedCategory R C) C where
  obj := ForgetEnrichment.to (Complex R)
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (S : Set (ModuleCategory R D)) [Small.{u} {M // S M}]

def dgModuleSubcategoryYoneda :
    DGFunctor R (RightModule R D) (RightModule R {M // S M}) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorRestrictedYoneda R {M // S M} (RightModule R D)
    ((dgFullSubcategoryInclusion R (ModuleCategory R D) S).comp
      (dgClosedObjectsForget R (RightModule R D)))

lemma dgModuleSubcategoryYoneda_obj (N : {M // S M}) :
    (dgModuleSubcategoryYoneda R D S).obj (ForgetEnrichment.to (Complex R) N.val) =
      representable R N := by
  apply EnrichedFunctor.ext (Complex R)
    (F := ((dgModuleSubcategoryYoneda R D S).obj
      (ForgetEnrichment.to (Complex R) N.val)).toFunctor)
    (G := (representable R N).toFunctor) (fun _ ↦ rfl)
  intro x y
  change (𝟙 _ ≫ (representable R (ForgetEnrichment.to (Complex R) N.val)).map
      (Opposite.op x.unop.val) (Opposite.op y.unop.val)) ≫ eqToHom (by rfl) =
        (representable R N).map x y
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

def dgModuleSubcategoryShiftIso
    (hS : ∀ M, S M → ∀ s : ℤ, S (M⟦s⟧)) (N : {M // S M}) (s : ℤ) :
    ForgetEnrichment.of (Complex R) (shiftModule s (representable R N)) ≅
      ForgetEnrichment.of (Complex R)
        (representable R (⟨N.val⟦s⟧, hS N.val N.property s⟩ : {M // S M})) := by
  let F := dgModuleSubcategoryYoneda R D S
  let N' : {M // S M} := ⟨N.val⟦s⟧, hS N.val N.property s⟩
  have hN : F.obj (ForgetEnrichment.to (Complex R) N.val) = representable R N :=
    dgModuleSubcategoryYoneda_obj R D S N
  have hN' : F.obj (shiftModule s (ForgetEnrichment.to (Complex R) N.val)) =
      representable R N' := dgModuleSubcategoryYoneda_obj R D S N'
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorShiftIso R D {M // S M} F s
    (ForgetEnrichment.to (Complex R) N.val)
  exact (eqToIso (congrArg
    (fun K ↦ ForgetEnrichment.of (Complex R) (shiftModule s K)) hN)).symm ≪≫
      e.symm ≪≫ eqToIso (congrArg (ForgetEnrichment.of (Complex R)) hN')

end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
