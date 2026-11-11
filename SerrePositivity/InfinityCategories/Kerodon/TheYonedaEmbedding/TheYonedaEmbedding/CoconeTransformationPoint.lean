module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationFatComparison

/-!
概要：指定した頂点の等式を保ち、元の余錐の変換の fat join 表示を計算する。
方針：頂点の Yoneda 族に全パラメータの比較式を適用する。
規約：余錐も指定頂点も選び直さない。
使われ方：ホモトピーから実現した余錐と元の変換の比較。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {K X : SSet.{u}} {f : K ⟶ X}

/-- 概要：元の余錐を指定頂点の余錐空間の点として表示する。
方針：指定された頂点の等式を fiber 条件に用いる。
規約：元の余錐そのもの。使われ方：頂点の実現に伴う等式の輸送。 -/
def coconeMappingPointAt (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f z) _⦋0⦌ :=
  ⟨c, by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero]; exact hv⟩

/-- 概要：元の余錐の変換の fat join 図式は元の join 表示の制限そのもの。
方針：全パラメータの比較の式と Yoneda の uncurry の一致を使う。
規約：指定頂点への等式を保持。使われ方：実現の相対ホモトピーの接続。 -/
lemma coconeTransformationPointAt_fatDiagram
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) (z : X _⦋0⦌) (hv : c.vertex = z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationFatDiagram (SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap f z).app _ (coconeMappingPointAt c z hv))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K Δ[0] ≫ c.val := by
  rw [← SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationFatDiagram_comparison,
    SSet.yonedaEquiv_symm_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (SSet.yonedaEquiv.symm c) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
