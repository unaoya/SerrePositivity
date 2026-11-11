module
public import SerrePositivity.KST.SConstruction.CubicalLambdaHorizontalCoherence
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition

/-! # native 関手族の各単体の実横合成と結合・単位
概要：元の全 Hom を保つ Λ の実逆関手を使い、native 横合成の全単体の法則を示す。
方針：二回の HA 抽出を厳密逆律で消去し、元の Λ の横合成等号へ帰着する。
規約：元の閉単位と増大を保持。使われ方：Kan 写像空間の結合・単位等号。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E B T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]

/-- 元の native 関手族の各単体を、Serre 対角と元の全次数横合成で合成する。 -/
def dgFunctorNativeComposeSimplex {N : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A E B) N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D B) N :=
  (cubicalLambdaNativeSimplex A
    (cubicalLambdaFunctorPair A (simplexHAInverseFunctor A s) (simplexHAInverseFunctor A t))).map
    (dgFunctorHorizontalDG A D E B)

omit [Small.{u} B] in
/-- 元の Kan 写像空間の横合成の各単体は、同じ元の native 単体の合成。 -/
lemma dgFunctorNativeComposition_app (n : SimplexCategoryᵒᵖ)
    (s : (dgFunctorNativeMappingSpace A D E).obj n)
    (t : (dgFunctorNativeMappingSpace A E B).obj n) :
    ((dgFunctorNativeComposition A D E B).app n (s, t)).val =
      dgFunctorNativeComposeSimplex A D E B s.val t.val := rfl

/-- 元の native 関手族の実横合成は、全単体で厳密に結合的。 -/
lemma dgFunctorNativeComposeSimplex_associativity {N : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A E B) N)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A B T) N) :
    dgFunctorNativeComposeSimplex A D B T (dgFunctorNativeComposeSimplex A D E B s t) r =
      dgFunctorNativeComposeSimplex A D E T s (dgFunctorNativeComposeSimplex A E B T t r) := by
  unfold dgFunctorNativeComposeSimplex
  simp only [← cubicalLambdaNativeSimplex_post, simplexHAInverseFunctor_native]
  exact congrArg (cubicalLambdaNativeSimplex A)
    (cubicalLambdaHorizontal_associativity A D E B T
      (simplexHAInverseFunctor A s) (simplexHAInverseFunctor A t) (simplexHAInverseFunctor A r))

omit [DGCategory A E] [DGCategory A B] [DGCategory A T] [Small.{u} E] [Small.{u} B] in
/-- 元の増大から元の恒等関手を選ぶ、全次数の native 単位単体。 -/
def dgFunctorNativeIdentitySimplex (N : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D D) N :=
  cubicalLambdaNativeSimplex A
    (DGFunctor.comp (cubicalLambdaCounit A (Δ[N] : SSet.{u})) (dgFunctorIdentityPoint A D))

omit [DGCategory A E] [DGCategory A B] [DGCategory A T] [Small.{u} E] [Small.{u} B] in
/-- 元の native 単位単体は、退化を含む全作用素で同じ単位単体を回収する。 -/
lemma dgFunctorNativeIdentitySimplex_pullback {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1)) :
    (dgFunctorNativeIdentitySimplex A D N).pullback α = dgFunctorNativeIdentitySimplex A D M := by
  unfold dgFunctorNativeIdentitySimplex
  rw [← cubicalLambdaNativeSimplex_precompose, ← strictDGFunctor_comp_assoc,
    cubicalLambdaCounit_naturality]

omit [DGCategory A E] [DGCategory A B] [DGCategory A T] [Small.{u} E] [Small.{u} B] in
/-- 元の native 単位零単体は、元の恒等 dg 関手の頂点。 -/
lemma dgFunctorNativeIdentitySimplex_zero :
    dgFunctorNativeIdentitySimplex A D 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (DGFunctor.id D) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] [Small.{u} E] in
/-- 元の native 単位単体との左横合成は、元の全 native 単体を回収する。 -/
lemma dgFunctorNativeComposeSimplex_left_unit {N : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N) :
    dgFunctorNativeComposeSimplex A D D E (dgFunctorNativeIdentitySimplex A D N) s = s := by
  unfold dgFunctorNativeComposeSimplex dgFunctorNativeIdentitySimplex
  rw [simplexHAInverseFunctor_native, ← cubicalLambdaNativeSimplex_post,
    cubicalLambdaHorizontal_left_unit, cubicalLambdaNativeSimplex_inverse]

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] in
/-- 元の native 単位単体との右横合成は、元の全 native 単体を回収する。 -/
lemma dgFunctorNativeComposeSimplex_right_unit {N : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (DGFunctor A D E) N) :
    dgFunctorNativeComposeSimplex A D E E s (dgFunctorNativeIdentitySimplex A E N) = s := by
  unfold dgFunctorNativeComposeSimplex dgFunctorNativeIdentitySimplex
  rw [simplexHAInverseFunctor_native, ← cubicalLambdaNativeSimplex_post,
    cubicalLambdaHorizontal_right_unit, cubicalLambdaNativeSimplex_inverse]

end SerrePositivity.KST.SConstruction
