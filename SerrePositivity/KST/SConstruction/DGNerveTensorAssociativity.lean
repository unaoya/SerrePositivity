module
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPairCoherence
public import SerrePositivity.KST.SConstruction.DGNerveTensorNaturality

/-! # native dg nerve の実 tensor 比較の結合則
概要：三つの native 入力からの tensor 比較は、実 dg tensor の結合関手と両立する。
方針：全 Hom を回収する厳密逆律で二回の抽出を消し、元の対角の結合則を使う。
規約：全単体的写像の等号。使われ方：dg 関手圏の横合成と豊穣入力の結合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E B : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B]

/-- Λ nerve の実 tensor 比較の二回適用は、実 dg 結合関手と直積の結合同型で一致。 -/
lemma cubicalLambdaNerveTensor_associativity :
    (cubicalLambdaNerveTensor A D E ⊗ₘ 𝟙 (cubicalLambdaNerve A B)) ≫
        cubicalLambdaNerveTensor A (DGTensorCategory A D E) B ≫
        cubicalLambdaNerveMap A (dgTensorAssociator A D E B) =
      (α_ (cubicalLambdaNerve A D) (cubicalLambdaNerve A E) (cubicalLambdaNerve A B)).hom ≫
        (𝟙 (cubicalLambdaNerve A D) ⊗ₘ cubicalLambdaNerveTensor A E B) ≫
        cubicalLambdaNerveTensor A D (DGTensorCategory A E B) := by
  ext n p
  rcases p with ⟨⟨F, G⟩, H⟩
  exact cubicalLambdaFunctorPair_associativity A F G H

/-- native tensor 比較の二回適用は、実 dg tensor の結合関手と全単体で一致。 -/
lemma dgNerveTensor_associativity :
    (dgNerveTensor A D E ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A B)) ≫
        dgNerveTensor A (DGTensorCategory A D E) B ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorAssociator A D E B) =
      (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A B)).hom ≫
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) ⊗ₘ dgNerveTensor A E B) ≫
        dgNerveTensor A D (DGTensorCategory A E B) := by
  ext n p
  rcases p with ⟨⟨s, t⟩, r⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n.unop.len at s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E n.unop.len at t
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A B n.unop.len at r
  change (cubicalLambdaNativeSimplex A
      (cubicalLambdaFunctorPair A
        (simplexHAInverseFunctor A (cubicalLambdaNativeSimplex A
          (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s)
            (simplexHAInverseFunctor A t)))) (simplexHAInverseFunctor A r))).map
      (dgTensorAssociator A D E B) =
    cubicalLambdaNativeSimplex A (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s)
      (simplexHAInverseFunctor A (cubicalLambdaNativeSimplex A
        (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A t) (simplexHAInverseFunctor A r)))))
  rw [simplexHAInverseFunctor_native, simplexHAInverseFunctor_native,
    ← cubicalLambdaNativeSimplex_post, cubicalLambdaFunctorPair_associativity]

end SerrePositivity.KST.SConstruction
