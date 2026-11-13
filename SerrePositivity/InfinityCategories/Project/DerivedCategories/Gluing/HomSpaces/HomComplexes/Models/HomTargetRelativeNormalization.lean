module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomTargetNormalizedPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomCoefficientAugmentationNormalization

/-!
概要：元終域の正規化 prism と係数 path を全パラメーター・両端固定で比較する。
方針：元係数の相対 homotopy を実 Hom 模型同型で輸送する。
規約：区間の両端で同じ実入力を保持する。使われ方：元二脚の lax Hom 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))

lemma dgGluingHomTargetNormalizedPrism_eq_coefficient :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedPrism R C D E p q X Y =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationPrism R C D M X Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom := by
  have h := congrArg (fun k => k ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedPrism_coefficient R C D E p q X Y)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetRelativeNormalization_exists :
    ∃ H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedPrism R C D E p q X Y)
        (uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y)),
      (((SSet.boundary 1).ι ▷ P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v}) ⊗ P) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ P) ≫
            uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y) := by
  obtain ⟨H, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientAugmentationNormalization_exists R C D M X Y
  let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  have he : uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomCoefficientIntervalPath R C D M X Y) ≫ e =
      uncurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y) := by
    exact (uncurry_natural_right _ _).symm
  let T := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H e
  let U := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget T
    (dgGluingHomTargetNormalizedPrism_eq_coefficient R C D E p q X Y).symm he
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc, he]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
