module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndImageStrongSaturation

/-!
概要：小さい辺族の強飽和生成閉包の全射圏は presentable。
方針：同じ compact 被覆を持つ実 Ind 像の強飽和性と最小性から、全頂点条件を同定する。
規約：局所置換や反射の存在は入力にしない。使われ方：HTT 5.5.4.14 から固定始域 fiber へ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 強飽和な実像が生成辺を含めば、元の生成閉包の辺クラスと一致する。 -/
lemma indArrowImageEdges_eq_generatedEdges
    {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G))
    (hgen : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
  apply Set.Subset.antisymm (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_subset_generatedEdges edges G)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_minimal _ hS
  rintro _ ⟨i, rfl⟩
  exact hgen i

/-- 辺クラスの一致は、元の全高次単体を保持した実像全部分圏の等式を与える。 -/
lemma indArrowImageCategory_eq_generatedArrowCategory
    {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges edges G = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory edges G = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges := by
  have hpred : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndArrowImageVertex edges G = fun f ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedEdges edges := by
    funext f
    apply propext
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_arrowVertex_iff edges G f, he]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageCategory, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory]
  rw [hpred]

/-- 元の presentable 圏の小さい辺族の強飽和射圏は、無条件に presentable。 -/
lemma generatedArrowCategory_isPresentable
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory edges) := by
  obtain ⟨κ, μ, _hκ, hμ, hlarge, _hb, _hCμ, _hend, A, hA, G,
    hff, hG, hcompact, hcover, hImage, hpres, hgen, hids, hpush, _hcancel, htri⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_triangleOperationsPresentableIndImage hC edges Cardinal.aleph0
  have := hA
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hS := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indArrowImageEdges_stronglySaturated hlarge edges hC.hasSmallColimits G
    hff hG hcompact hcover hImage.hasSmallColimits hpres hids hpush htri
  have he := indArrowImageEdges_eq_generatedEdges edges G hS hgen
  have hcat := indArrowImageCategory_eq_generatedArrowCategory edges G he
  exact hImage.of_equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso hcat))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.4.14" (partial := direction) "仮定：presentable C と小生成な強飽和 S（HTT と一致、小生成性の定義の辺族を用いる）。結論：同じ S の全射準圏が presentable、従って accessible という (3)⇒(2)⇒(1)（一致）。accessible な任意の強飽和射圏から小生成族を回収する逆向きは結論しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory_isPresentable
attribute [cite HTT "5.5.5.9" (partial := stronger-hyp) "仮定：presentable C と小生成飽和 S（Lean が強い：S は小さい辺族の強飽和生成閉包）。結論：同じ S の全射準圏の presentability（この場合の小生成性から表示可能性に一致）。任意の飽和生成閉包や逆向きの生成族回収は結論しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatedArrowCategory_isPresentable
