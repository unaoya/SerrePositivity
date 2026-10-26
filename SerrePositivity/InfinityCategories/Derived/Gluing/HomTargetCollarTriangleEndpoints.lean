module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.ExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapGeometry
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetIdentityCommaProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleTimeConstantFace
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y

attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetOriginalHomSquare :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ P) ⟶ dgNerve R E :=
  (Δ[1] ◁ dgGluingHomTargetHomIntervalEvaluation R C D E p q X Y) ≫
    (β_ (Δ[1] : SSet.{max (u + 1) v})
      (dgNerve R (DGGluingObject R C D M))).hom ≫
        (dgGluingHomTargetAugmentationHomotopy R C D E p q).h

lemma dgGluingHomTargetArrowTriangle_original_square (i : Fin 2) :
    (squareTriangle i ▷ P) ≫
      intervalFunctorHomPrism (dgGluingHomTargetArrowIntervalComparison R C D E p q X Y) =
    (squareTriangle i.rev ▷ P) ≫ (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫
      dgGluingHomTargetOriginalHomSquare R C D E p q X Y := by
  have hs := congrArg (fun k => (k ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫
        dgGluingHomTargetOriginalHomSquare R C D E p q X Y)
    (dgGluingSquareTriangle_swap.{max (u + 1) v} i)
  rw [dgGluingHomTargetArrowIntervalComparison_prism]
  simpa only [comp_whiskerRight, Category.assoc, dgGluingHomTargetOriginalHomSquare] using hs

lemma dgGluingHomTargetPreCollarTriangle_one :
    (Δ[2] ◁ (ι₁ : P ⟶ _)) ≫
      dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    (dgGluingHomTargetArrowTriangles R C D E p q X Y).first := by
  have h := dgGluingPreNormalizeUnitCollarTriangleFamily_one.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have he := congrArg (fun k => (squareTriangle (1 : Fin 2) ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫ k)
    (dgGluingHomTargetNormalization_original_square R C D E p q X Y)
  have ht := dgGluingHomTargetArrowTriangle_original_square R C D E p q X Y 0
  exact h.trans (he.trans ht.symm)

lemma dgGluingHomTargetExitCollarTriangle_zero :
    (Δ[2] ◁ (ι₀ : P ⟶ _)) ≫
      dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    (dgGluingHomTargetArrowTriangles R C D E p q X Y).second := by
  have h := dgGluingExitUnitCollarTriangleFamily_zero.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have he := congrArg (fun k => (squareTriangle (0 : Fin 2) ▷ P) ≫
      (α_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1] P).hom ≫ k)
    (dgGluingHomTargetNormalization_original_square R C D E p q X Y)
  have ht := dgGluingHomTargetArrowTriangle_original_square R C D E p q X Y 1
  exact h.trans (he.trans ht.symm)

lemma dgGluingHomTargetArrowTriangles_first_variable :
    (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
      (dgGluingHomTargetArrowTriangles R C D E p q X Y).first =
    intervalMappingUncurry
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
        dgGluingHomTargetRightIntervalInput R C D E p q X Y) := by
  have hV := dgGluingPreNormalizeUnitCollarTriangleFamily_last_input.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  rw [intervalMappingUncurry_precomp] at hV
  have h := dgGluingTriangleConstantFace_endpoint (0 : Fin 3) (1 : Fin 2) _ _ hV
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at h
  erw [dgGluingHomTargetPreCollarTriangle_one R C D E p q X Y] at h
  exact h.symm.trans (congrArg intervalMappingUncurry
    (dgGluingHomTargetNormalizationSourceIntervalFamily R C D E p q X Y))

lemma dgGluingHomTargetArrowTriangles_second_variable :
    (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
      (dgGluingHomTargetArrowTriangles R C D E p q X Y).second =
    intervalMappingUncurry
      (complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
        dgGluingHomTargetLeftIntervalInput R C D E p q X Y) := by
  have hV := dgGluingExitUnitCollarTriangleFamily_first_original.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  rw [intervalMappingUncurry_precomp] at hV
  have h := dgGluingTriangleConstantFace_endpoint (2 : Fin 3) (0 : Fin 2) _ _ hV
  simp only [ite_true] at h
  erw [dgGluingHomTargetExitCollarTriangle_zero R C D E p q X Y] at h
  exact h.symm.trans (congrArg intervalMappingUncurry
    (dgGluingHomTargetNormalizationReplacementIntervalFamily R C D E p q X Y))

end SerrePositivity.InfinityCategories
