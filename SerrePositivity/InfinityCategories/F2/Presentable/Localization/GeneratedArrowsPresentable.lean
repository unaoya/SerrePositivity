module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageStrongSaturation

/-!
概要：小さい辺族の強飽和生成閉包の全射圏は presentable。
方針：同じ compact 被覆を持つ実 Ind 像の強飽和性と最小性から、全頂点条件を同定する。
規約：局所置換や反射の存在は入力にしない。使われ方：HTT 5.5.4.14 から固定始域 fiber へ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 強飽和な実像が生成辺を含めば、元の生成閉包の辺クラスと一致する。 -/
lemma indArrowImageEdges_eq_generatedEdges
    {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hS : IsStronglySaturatedEdgeSetOfShapes (SSet.uliftFunctor.{u + 1, u}).obj
      (indArrowImageEdges edges G))
    (hgen : ∀ i, IndArrowImageVertex edges G (generatorArrowVertex edges i)) :
    indArrowImageEdges edges G = generatedEdges edges := by
  apply Set.Subset.antisymm (indArrowImageEdges_subset_generatedEdges edges G)
  apply stronglySaturatedClosure_minimal _ hS
  rintro _ ⟨i, rfl⟩
  exact hgen i

/-- 辺クラスの一致は、元の全高次単体を保持した実像全部分圏の等式を与える。 -/
lemma indArrowImageCategory_eq_generatedArrowCategory
    {μ : Cardinal.{u}} [Fact μ.IsRegular] {A : SSet.{u}} [Quasicategory A]
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (he : indArrowImageEdges edges G = generatedEdges edges) :
    indArrowImageCategory edges G = generatedArrowCategory edges := by
  have hpred : IndArrowImageVertex edges G = fun f ↦ arrowVertexEdge f ∈ generatedEdges edges := by
    funext f
    apply propext
    rw [← indArrowImageEdges_arrowVertex_iff edges G f, he]
  dsimp only [indArrowImageCategory, generatedArrowCategory]
  rw [hpred]

/-- 元の presentable 圏の小さい辺族の強飽和射圏は、無条件に presentable。 -/
lemma generatedArrowCategory_isPresentable
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (generatedArrowCategory edges) := by
  obtain ⟨κ, μ, _hκ, hμ, hlarge, _hb, _hCμ, _hend, A, hA, G,
    hff, hG, hcompact, hcover, hImage, hpres, hgen, hids, hpush, _hcancel, htri⟩ :=
    exists_triangleOperationsPresentableIndImage hC edges Cardinal.aleph0
  have := hA
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hS := indArrowImageEdges_stronglySaturated hlarge edges hC.hasSmallColimits G
    hff hG hcompact hcover hImage.hasSmallColimits hpres hids hpush htri
  have he := indArrowImageEdges_eq_generatedEdges edges G hS hgen
  have hcat := indArrowImageCategory_eq_generatedArrowCategory edges G he
  exact hImage.of_equivalence (qCatEquivalenceOfIso (eqToIso hcat))

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
