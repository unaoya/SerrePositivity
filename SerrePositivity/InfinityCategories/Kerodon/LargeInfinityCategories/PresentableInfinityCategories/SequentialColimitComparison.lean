module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialCofinalSubsequences
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：一つの全可算列の二つの共終部分列の指定余極限頂点を比較する。
方針：同じ元の列の余極限錐を両部分列へ制限し、全余錐の普遍比較を使う。
規約：標的は slice 圏でもよく、元の頂点を保持する。
使われ方：引き戻しの二成分を交互列の共通余極限で同期する。

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

/-- 概要：指定した共終部分列の余極限頂点は、元の全列の指定余極限頂点と同型。
方針：元の全余錐を native な right cofinal 写像で制限し、余極限頂点の普遍比較を取る。
規約：元の全列と指定された二つの余錐を使う。
使われ方：交互列の片方の成分の余極限比較。 -/
def sequentialSubsequenceColimitVertexIso (a : ℕ → ℕ) (ha : Monotone a)
    (hcofinal : ∀ k, ∃ n, k ≤ a n)
    {C : SSet.{u + 1}} [Quasicategory C]
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha)) ≫ F))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex c.vertex := by
  let r := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha))
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal r := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequence_nerve_isRightCofinal a ha hcofinal)
  have hcr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict r) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal r hr c).mp hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso d (c.restrict r) hd hcr

/-- 概要：同じ全列の任意の二つの共終部分列の余極限頂点は同型。
方針：元の全列の余極限を選び、その同じ頂点を経由して二つの普遍比較を合成する。
規約：余極限存在は標的の小余完備性だけから得る。
使われ方：偶数・奇数の両成分を同じ余極限で同一視する。 -/
lemma nonempty_subsequenceColimitVertexIso (a b : ℕ → ℕ) (ha : Monotone a) (hb : Monotone b)
    (hca : ∀ k, ∃ n, k ≤ a n) (hcb : ∀ k, ∃ n, k ≤ b n)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    {F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} a ha)) ≫ F))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u} b hb)) ≫ F))
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone e) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex e.vertex) := by
  obtain ⟨c, hc⟩ := hC (nerve (ULift.{u} ℕ)) F
  exact ⟨sequentialSubsequenceColimitVertexIso a ha hca c hc d hd ≪≫
    (sequentialSubsequenceColimitVertexIso b hb hcb c hc e he).symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
