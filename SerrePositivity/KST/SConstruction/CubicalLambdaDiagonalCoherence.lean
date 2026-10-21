module
public import SerrePositivity.KST.SConstruction.CubicalLambdaDiagonal
public import SerrePositivity.KST.SConstruction.DGTensorAssociator

/-! # Λ の実 dg 対角関手の結合則
概要：元の Serre 対角の二回適用が、実 dg tensor の結合関手と厳密に両立する。
方針：実 dg 関手の同値判定を使い、全 Hom 上で元の余モノイドの結合則を回収する。
規約：対象は同じ三対象、Hom は元の三因子。使われ方：Λ の oplax tensor の結合則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の対角 dg 関手の二回適用は、元の三重 dg tensor の結合関手と両立する。 -/
lemma cubicalLambdaDiagonal_associativity (K : SSet.{u}) :
    DGFunctor.comp
        (DGFunctor.comp (cubicalLambdaDiagonal A K)
          (dgTensorFunctor A (cubicalLambdaDiagonal A K)
            (DGFunctor.id (CubicalLambda A K))))
        (dgTensorAssociator A (CubicalLambda A K) (CubicalLambda A K) (CubicalLambda A K)) =
      DGFunctor.comp (cubicalLambdaDiagonal A K)
        (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K)) (cubicalLambdaDiagonal A K)) := by
  refine EnrichedFunctor.ext (Complex A)
    (F := DGFunctor.comp
      (DGFunctor.comp (cubicalLambdaDiagonal A K)
        (dgTensorFunctor A (cubicalLambdaDiagonal A K) (DGFunctor.id (CubicalLambda A K))))
      (dgTensorAssociator A (CubicalLambda A K) (CubicalLambda A K) (CubicalLambda A K)))
    (G := DGFunctor.comp (cubicalLambdaDiagonal A K)
      (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K)) (cubicalLambdaDiagonal A K)))
    (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans
    (comonoidDiagonal_associativity (cubicalLambdaHomComonoid A K x y))

end SerrePositivity.KST.SConstruction
