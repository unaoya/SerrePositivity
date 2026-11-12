module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveTensor
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveNativeNaturality

/-! # native dg nerve の実 tensor 比較の二変数自然性
概要：native の直積から実 tensor への比較は、両方の厳密 dg 入力写像について自然。
方針：元の全 Hom を持つ逆関手の後合成則と Serre 対角による組の後合成則を使う。
規約：全退化と全 Hom を保持。使われ方：dg 関手圏の横合成と豊穣 K の入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D E B C : Type v}
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [DGCategory A C]

/-- Λ nerve の直積から実 tensor への比較は、両方の厳密 dg 後合成で自然。 -/
lemma cubicalLambdaNerveTensor_naturality (F : DGFunctor A D B) (G : DGFunctor A E C) :
    (cubicalLambdaNerveMap A F ⊗ₘ cubicalLambdaNerveMap A G) ≫
        cubicalLambdaNerveTensor A B C =
      cubicalLambdaNerveTensor A D E ≫ cubicalLambdaNerveMap A (dgTensorFunctor A F G) := by
  ext n p
  exact cubicalLambdaFunctorPair_post A p.1 p.2 F G

/-- native の直積から実 tensor への比較は、二つの厳密 dg 入力写像について自然。 -/
lemma dgNerveTensor_naturality (F : DGFunctor A D B) (G : DGFunctor A E C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) ≫ dgNerveTensor A B C =
      dgNerveTensor A D E ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgTensorFunctor A F G) := by
  ext n p
  rcases p with ⟨s, t⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n.unop.len at s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E n.unop.len at t
  change cubicalLambdaNativeSimplex A
      (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A (s.map F))
        (simplexHAInverseFunctor A (t.map G))) =
    (cubicalLambdaNativeSimplex A
      (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s)
        (simplexHAInverseFunctor A t))).map (dgTensorFunctor A F G)
  rw [simplexHAInverseFunctor_post, simplexHAInverseFunctor_post,
    cubicalLambdaFunctorPair_post, cubicalLambdaNativeSimplex_post]

end SerrePositivity.KST.SConstruction
