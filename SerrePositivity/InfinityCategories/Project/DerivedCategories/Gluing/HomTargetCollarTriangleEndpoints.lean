module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetArrowPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapGeometry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetIdentityCommaProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TriangleTimeConstantFace
/-!
概要：元終域の両補正三角形の元端を、指定矢印 Hom の実二三角形へ同定する。
方針：元正方形の全族の一致と、二区間の交換の厳密再添字を使う。
規約：二辺だけでなく全三角形を保持する。使われ方：元入力付き道の端点照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetOriginalHomSquare :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ P) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E :=
  (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomIntervalEvaluation R C D E p q X Y) ≫
    (β_ (Δ[1] : SSet.{max (u + 1) v})
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationHomotopy R C D E p q).h

lemma dgGluingHomTargetArrowTriangle_original_square (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowIntervalComparison R C D E p q X Y) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i.rev ▷ P) ≫ (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫
      dgGluingHomTargetOriginalHomSquare R C D E p q X Y := by
  have hs := congrArg (fun k => (k ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫
        dgGluingHomTargetOriginalHomSquare R C D E p q X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSquareTriangle_swap.{max (u + 1) v} i)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowIntervalComparison_prism]
  simpa only [comp_whiskerRight, Category.assoc, dgGluingHomTargetOriginalHomSquare] using hs

lemma dgGluingHomTargetPreCollarTriangle_one :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowTriangles R C D E p q X Y).first := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily_one.{u, max (u + 1) v}
    R E IX IY (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have he := congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (1 : Fin 2) ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalization_original_square R C D E p q X Y)
  have ht := dgGluingHomTargetArrowTriangle_original_square R C D E p q X Y 0
  exact h.trans (he.trans ht.symm)

lemma dgGluingHomTargetExitCollarTriangle_zero :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowTriangles R C D E p q X Y).second := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily_zero.{u, max (u + 1) v}
    R E IX IY (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have he := congrArg (fun k => (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle (0 : Fin 2) ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalization_original_square R C D E p q X Y)
  have ht := dgGluingHomTargetArrowTriangle_original_square R C D E p q X Y 1
  exact h.trans (he.trans ht.symm)

lemma dgGluingHomTargetArrowTriangles_first_variable :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowTriangles R C D E p q X Y).first =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetRightIntervalInput R C D E p q X Y) := by
  have hV := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeUnitCollarTriangleFamily_last_input.{u, max (u + 1) v}
    R E IX IY (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp] at hV
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleConstantFace_endpoint (0 : Fin 3) (1 : Fin 2) _ _ hV
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at h
  erw [dgGluingHomTargetPreCollarTriangle_one R C D E p q X Y] at h
  exact h.symm.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationSourceIntervalFamily R C D E p q X Y))

lemma dgGluingHomTargetArrowTriangles_second_variable :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetArrowTriangles R C D E p q X Y).second =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLeftIntervalInput R C D E p q X Y) := by
  have hV := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitUnitCollarTriangleFamily_first_original.{u, max (u + 1) v}
    R E IX IY (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp] at hV
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleConstantFace_endpoint (2 : Fin 3) (0 : Fin 2) _ _ hV
  simp only [ite_true] at h
  erw [dgGluingHomTargetExitCollarTriangle_zero R C D E p q X Y] at h
  exact h.symm.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationReplacementIntervalFamily R C D E p q X Y))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
