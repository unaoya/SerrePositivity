module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialColimitComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：同じ全交互列の二つの部分列を実現する関手像の余極限頂点を同型にする。
方針：元の全関手同型で指定余錐を輸送し、同じ共終部分列比較を適用する。
規約：各点だけの比較で全図式同型を代用しない。
使われ方：引き戻しの両成分の余極限の標的像を同期する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：同じ交互列の共終部分列を与える二つの関手像の余極限頂点は同型。
方針：元の指定余錐の像を全図式同型で輸送し、共通全列の余極限を経由する。
規約：始域・標的の accessibility を入力にせず、小余極限保存だけを使う。
使われ方：compact な成分の可算表示を引き戻し内で同期する。 -/
lemma nonempty_subsequenceImageColimitIso
    (a b : ℕ → ℕ) (ha : Monotone a) (hb : Monotone b)
    (hca : ∀ k, ∃ n, k ≤ a n) (hcb : ∀ k, ∃ n, k ≤ b n)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B) (p : E ⟶ B) (q : D ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hq : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q)
    {FE : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ E}
    {FD : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ D}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ B}
    (eE : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (FE ≫ p) ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha)) ≫ F))
    (eD : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (FD ≫ q) ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} b hb)) ≫ F))
    (cE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone FE) (hcE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cE)
    (cD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone FD) (hcD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cD) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (p.app (Opposite.op ⦋0⦌) cE.vertex)
      (q.app (Opposite.op ⦋0⦌) cD.vertex)) := by
  have hpE := hp (nerve (ULift.{u} ℕ)) FE cE hcE
  have hqD := hq (nerve (ULift.{u} ℕ)) FD cD hcD
  let dE := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso eE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone p cE) hpE
  let dD := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso eD (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q cD) hqD
  have hdE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dE := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso_isColimit _ _ _
  have hdD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone dD := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso_isColimit _ _ _
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nonempty_subsequenceColimitVertexIso a b ha hb hca hcb hB dE hdE dD hdD
  exact ⟨by
    simpa only [dE, dD, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex] using e⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
