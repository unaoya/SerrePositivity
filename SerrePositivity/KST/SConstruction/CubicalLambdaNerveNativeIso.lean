module
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerve

/-! # 元の Λ 実 dg 関手 nerve と native HA dg nerve の実単体同型
概要：元の各次数の実逆対応は、全作用素・退化を保つ単体集合の同型となる。
方針：元の全成分自然性に、元の両厳密逆律を持つ各次数の同型を使う。
規約：元の対象・Hom・次数と実前合成を保持。使われ方：native 直積と tensor source 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の全 Λ 実 dg 関手と元の native HA dg nerve の、全退化を保つ実単体同型。 -/
def cubicalLambdaNerveNativeIso : cubicalLambdaNerve A D ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  NatIso.ofComponents (fun n => (cubicalLambdaNativeSimplexEquiv A (D := D) n.unop.len).toIso)
    (by
      intro X Y f
      ext F
      exact cubicalLambdaNativeSimplex_precompose A F f.unop.toOrderHom)

/-- 元の実単体同型の順射は、元の全 HA 成分を持つ native 単体の抽出そのもの。 -/
lemma cubicalLambdaNerveNativeIso_hom_app {N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D) :
    (cubicalLambdaNerveNativeIso A D).hom.app (op ⦋N⦌) F = cubicalLambdaNativeSimplex A F := rfl

/-- 元の実単体同型の逆射は、元の全 Hom を持つ実逆 dg 関手そのもの。 -/
lemma cubicalLambdaNerveNativeIso_inv_app {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    (cubicalLambdaNerveNativeIso A D).inv.app (op ⦋N⦌) s = simplexHAInverseFunctor A s := rfl

end SerrePositivity.KST.SConstruction
