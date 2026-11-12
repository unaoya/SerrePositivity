module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeInjectiveNaturality
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeCollapsedHigher
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeCollapsedPair

/-! # 元の全単体作用素・退化での native HA 比較の厳密自然性
概要：元の任意の単体作用素の Λ 前合成は、元の native HA 引き戻しと厳密に可換。
方針：部分集合上単射・潰れる二点・非単射高次の実三分岐を束ね、実両逆律を使う。
規約：全作用素と退化を保持。使われ方：元の単体集合の実比較同型と tensor 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の任意の単体作用素の Λ 前合成は、元の全 native HA 成分の引き戻しと一致。 -/
lemma cubicalLambdaNativeSimplexData_precompose {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) :
    cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F) =
      (cubicalLambdaNativeSimplexData A F).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    by_cases hi : Set.InjOn α (I : Set (Fin (M + 1)))
    · exact cubicalLambdaNativeSimplexData_precompose_hom_of_inj A F α I a b k hI ha hb hk hi
    · by_cases hc : I.card = 2
      · exact cubicalLambdaNativeSimplexData_precompose_hom_of_collapsed_pair A F α I a b k
          hI ha hb hk hi hc
      · exact cubicalLambdaNativeSimplexData_precompose_hom_of_not_inj A F α I a b k
          hI ha hb hk hi hc

/-- 元の退化を含む全単体作用素で、実 dg 関手からの native HA 単体の比較は自然。 -/
lemma cubicalLambdaNativeSimplex_precompose {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) :
    cubicalLambdaNativeSimplex A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F) =
      (cubicalLambdaNativeSimplex A F).pullback α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (cubicalLambdaNativeSimplexData_precompose A F α)

/-- 元の退化を含む全単体作用素で、native HA 単体からの実逆 dg 関手も厳密に自然。 -/
lemma simplexHAInverseFunctor_pullback {M N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (α : Fin (M + 1) →o Fin (N + 1)) :
    simplexHAInverseFunctor A (s.pullback α) = DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α)))
        (simplexHAInverseFunctor A s) := by
  have h := (cubicalLambdaNativeSimplex_precompose A (simplexHAInverseFunctor A s) α).trans
    (congrArg (fun t => t.pullback α) (cubicalLambdaNativeSimplex_inverse A s))
  exact (congrArg (simplexHAInverseFunctor A) h).symm.trans (simplexHAInverseFunctor_native A _)

end SerrePositivity.KST.SConstruction
