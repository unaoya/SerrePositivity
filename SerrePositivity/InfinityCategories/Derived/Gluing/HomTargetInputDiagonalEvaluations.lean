module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputTriangleEvaluations
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputDiagonals
/-!
概要：元入力付き四補正道の対角を、同じ実三角形の対角評価へ戻す。
方針：合成対応の対角評価と uncurry の自然性を使う。
規約：全時間と元入力を保持する。使われ方：共有四面体の六片の端点固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetFirstInputTriangleEvaluation_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ dgGluingHomTargetFirstInputFiber R C D E p q X Y) ≫
      dgGluingHomTargetFirstInputTriangleEvaluation R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  exact dgGluingFirstRestrictedTriangleEvaluation_diagonal
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (Simplex.vertex (q.obj Y.right)) (dgGluingHomTargetRightIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetLastInputTriangleEvaluation_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ dgGluingHomTargetLastInputFiber R C D E p q X Y) ≫
      dgGluingHomTargetLastInputTriangleEvaluation R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  exact dgGluingLastRestrictedTriangleEvaluation_diagonal (Z := dgNerve R E)
    (Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y)

lemma dgGluingHomTargetPreNormalizationInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingPreNormalizeUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    intervalMappingUncurry (dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [← dgGluingHomTargetPreNormalizationInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetFirstInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingHomTargetPreCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingPreUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    intervalMappingUncurry (dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [← dgGluingHomTargetPreCapInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetFirstInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingHomTargetExitCollarInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingExitUnitCollarTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    intervalMappingUncurry (dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [← dgGluingHomTargetExitCollarInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetLastInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← intervalMappingUncurry_precomp]

lemma dgGluingHomTargetExitCapInputPath_diagonal_evaluation :
    (stdSimplex.δ (1 : Fin 3) ▷ (P ⊗ Δ[1])) ≫
      dgGluingExitUnitCapTriangleFamily.{u, max (u + 1) v} R E IX IY
        (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    intervalMappingUncurry (dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [← dgGluingHomTargetExitCapInputPath_evaluation R C D E p q X Y,
    ← Category.assoc, ← whisker_exchange, Category.assoc]
  erw [dgGluingHomTargetLastInputTriangleEvaluation_diagonal R C D E p q X Y,
    ← intervalMappingUncurry_precomp]

end SerrePositivity.InfinityCategories
