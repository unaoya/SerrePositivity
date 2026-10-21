module

public import SerrePositivity.InfinityCategories.F1.CompositionCorrespondenceDiagonalPullback
public import SerrePositivity.InfinityCategories.F1.VertexFiberIsPullbackIso
public import SerrePositivity.InfinityCategories.F1.LeftFiberKan

/-!
概要：合成三角形の同じ対角 fiber を、指定外ホーンの延長 fiber と同定する。
方針：検証済みの実際の pullback に、同じ頂点 fiber の普遍性を適用する。
規約：元の三角形への射と、対角の指定頂点を保持する。
使われ方：後合成 fiber と指定外ホーン fiber の比較を、合成三角形全体へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (b : (intervalMappingSpace x z) _⦋0⦌)

/-- 同じ対角の指定頂点上の fiber は、同じ指定外ホーンの延長 fiber と厳密に同型。 -/
def compositionCorrespondenceFiberIso :
    vertexFiber (compositionCorrespondenceDiagonal x g) b ≅
      vertexFiber ((pre (horn 2 2).ι).app X)
        ((cospanHomHornMap x g).app (Opposite.op ⦋0⦌) b) :=
  vertexFiberIsoOfIsPullback (compositionCorrespondenceDiagonal_isPullback x g) b

/-- 同じ fiber 同型は、元の三角形への実際の射を保持する。 -/
lemma compositionCorrespondenceFiberIso_hom_ι :
    (compositionCorrespondenceFiberIso x g b).hom ≫
        vertexFiberι ((pre (horn 2 2).ι).app X)
          ((cospanHomHornMap x g).app (Opposite.op ⦋0⦌) b) =
      vertexFiberι (compositionCorrespondenceDiagonal x g) b ≫
        pullback.fst ((pre (horn 2 1).ι).app X) (composableHomHornMap x g) :=
  vertexFiberIsoOfIsPullback_hom_ι (compositionCorrespondenceDiagonal_isPullback x g) b

/-- 同じ対角 fiber は、元の対角評価の Kan 性から Kan 複体になる。 -/
lemma compositionCorrespondenceFiber_kanComplex [Quasicategory X] :
    KanComplex (vertexFiber (compositionCorrespondenceDiagonal x g) b) := by
  letI := compositionCorrespondenceDiagonal_fibration x g
  exact vertexFiber_kanComplex_of_leftFibration _ _

end SerrePositivity.InfinityCategories
