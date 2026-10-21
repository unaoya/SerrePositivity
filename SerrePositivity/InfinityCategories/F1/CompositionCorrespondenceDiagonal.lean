module

public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceFaces
public import SerrePositivity.InfinityCategories.F1.IntervalMappingVertexFaceCurry
public import SerrePositivity.InfinityCategories.F1.CompositionTriangleEndpoints

/-!
概要：合成三角形全体の同じ対角を、元の両端間の Hom 空間への射にする。
方針：二つの固定頂点を標準単体の面の合成則で計算し、元の対角族を curry する。
規約：合成辺を新しく選ばず、同じ普遍三角形の対角を使う。
使われ方：後合成 fiber を同じ対角上の三角形延長 fiber と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
local notation "T" => compositionCorrespondence x g

/-- 同じ普遍合成三角形の対角の始点は、元の第一辺の始点。 -/
lemma compositionCorrespondenceEvaluation_diagonal_source :
    (stdSimplex.δ (1 : Fin 2) ▷ T) ≫ (stdSimplex.δ (1 : Fin 3) ▷ T) ≫
        compositionCorrespondenceEvaluation x g =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm x := by
  have hδ : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    compositionCorrespondenceEvaluation_first, intervalMappingUncurry_face_source]

/-- 同じ普遍合成三角形の対角の終点は、元の指定第二辺の終点。 -/
lemma compositionCorrespondenceEvaluation_diagonal_target :
    (stdSimplex.δ (0 : Fin 2) ▷ T) ≫ (stdSimplex.δ (1 : Fin 3) ▷ T) ≫
        compositionCorrespondenceEvaluation x g =
      fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm z := by
  have hδ : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [← Category.assoc, ← comp_whiskerRight, hδ, comp_whiskerRight, Category.assoc,
    compositionCorrespondenceEvaluation_last, edgeFamily_target]

/-- 同じ全合成三角形から、その元の対角への評価。 -/
def compositionCorrespondenceDiagonal : T ⟶ intervalMappingSpace x z :=
  intervalMappingCurryOfVertexFaces
    ((stdSimplex.δ (1 : Fin 3) ▷ T) ≫ compositionCorrespondenceEvaluation x g)
    (compositionCorrespondenceEvaluation_diagonal_source x g)
    (compositionCorrespondenceEvaluation_diagonal_target x g)

/-- 対角評価を展開すると、元の普遍合成三角形の対角そのもの。 -/
lemma compositionCorrespondenceDiagonal_uncurry :
    intervalMappingUncurry (compositionCorrespondenceDiagonal x g) =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ compositionCorrespondenceEvaluation x g := by
  unfold compositionCorrespondenceDiagonal
  rw [intervalMappingCurryOfVertexFaces_uncurry]

end SerrePositivity.InfinityCategories
