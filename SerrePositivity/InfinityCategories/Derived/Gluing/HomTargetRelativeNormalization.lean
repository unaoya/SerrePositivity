module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizedPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomCoefficientAugmentationNormalization

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => (complexPinchedSpace
  (dgGluingHomComplex R C D M X Y))

lemma dgGluingHomTargetNormalizedPrism_eq_coefficient :
    dgGluingHomTargetNormalizedPrism R C D E p q X Y =
      dgGluingHomCoefficientAugmentationPrism R C D M X Y ≫
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom := by
  have h := congrArg (fun k => k ≫
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom)
    (dgGluingHomTargetNormalizedPrism_coefficient R C D E p q X Y)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetRelativeNormalization_exists :
    ∃ H : SSet.Homotopy (dgGluingHomTargetNormalizedPrism R C D E p q X Y)
        (uncurry (dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y)),
      (((SSet.boundary 1).ι ▷ P) ▷ (Δ[1] : SSet.{max (u + 1) v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max (u + 1) v}) ⊗ P) Δ[1] ≫
          ((SSet.boundary 1).ι ▷ P) ≫
            uncurry (dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y) := by
  obtain ⟨H, hH⟩ := dgGluingHomCoefficientAugmentationNormalization_exists R C D M X Y
  let e := (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  have he : uncurry (dgGluingHomCoefficientIntervalPath R C D M X Y) ≫ e =
      uncurry (dgGluingHomTargetCoefficientIntervalPath R C D E p q X Y) := by
    exact (uncurry_natural_right _ _).symm
  let T := functorHomotopyPostcomp H e
  let U := stableHomotopyRetarget T
    (dgGluingHomTargetNormalizedPrism_eq_coefficient R C D E p q X Y).symm he
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ e := dgGluingHomotopyRetarget_h T _ _
  rw [hU, ← Category.assoc, hH, Category.assoc, Category.assoc, he]

end SerrePositivity.InfinityCategories
