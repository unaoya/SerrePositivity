module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeInjectiveComponent
public import SerrePositivity.KST.SConstruction.SimplexHANativeInverse

/-! # 元の全単射な単体作用素での native HA 実比較の自然性
概要：単射な元の単体作用素の Λ 前合成と native HA 引き戻しは、元の全成分で一致。
方針：各部分集合上の単射成分を束ね、実両逆律で逆構成へ自然性を移す。
規約：元の単射作用素を明記。使われ方：全作用素・退化を含む単体的比較の構成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の単射な単体作用素の Λ 前合成と native HA 引き戻しは、元の全成分で一致。 -/
lemma cubicalLambdaNativeSimplexData_precompose_of_inj {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (hi : Function.Injective α) :
    cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F) =
      (cubicalLambdaNativeSimplexData A F).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    exact cubicalLambdaNativeSimplexData_precompose_hom_of_inj A F α I a b k hI ha hb hk hi.injOn

/-- 元の単射な全単体作用素に対し、実 dg 関手からの native HA 単体の比較は自然。 -/
lemma cubicalLambdaNativeSimplex_precompose_of_inj {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (hi : Function.Injective α) :
    cubicalLambdaNativeSimplex A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F) =
      (cubicalLambdaNativeSimplex A F).pullback α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (cubicalLambdaNativeSimplexData_precompose_of_inj A F α hi)

/-- 元の単射な全単体作用素に対し、native HA 単体からの実逆 dg 関手の比較も自然。 -/
lemma simplexHAInverseFunctor_pullback_of_inj {M N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (α : Fin (M + 1) →o Fin (N + 1)) (hi : Function.Injective α) :
    simplexHAInverseFunctor A (s.pullback α) = DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α)))
        (simplexHAInverseFunctor A s) := by
  have h := (cubicalLambdaNativeSimplex_precompose_of_inj A
    (simplexHAInverseFunctor A s) α hi).trans
    (congrArg (fun t => t.pullback α) (cubicalLambdaNativeSimplex_inverse A s))
  exact (congrArg (simplexHAInverseFunctor A) h).symm.trans (simplexHAInverseFunctor_native A _)

end SerrePositivity.KST.SConstruction
