module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredClosure
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullCoconeLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso

/-!
概要：元の局所対象全部分圏の filtered 余極限を周囲と同じ余錐から構成する。
方針：閉性で余極限頂点の局所性を得て全部分圏へ持ち上げ、全余錐比較で包含の保存を示す。
規約：局所置換反射を仮定しない。
使われ方：共通の正則濃度での局所対象包含の accessibility。

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


/-- 概要：共通 compact 端点の濃度で元の局所対象図式は内部の余極限を持つ。
方針：周囲の同じ余極限余錐を閉性により持ち上げる。
規約：同じ全図式と元の全部分圏を使用する。
使われ方：局所対象圏の filtered 余完備性。 -/
lemma hasColimit_of_compactEndpoints {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hends : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i)))
    {K : SSet.{u}} [Quasicategory K] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι d = c := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) c.vertex :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalObject_colimit_of_compactEndpoints edges hends _ c hc
      (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (D.app _ (ULift.up k)))
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCoconeLift _ D c hv, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCoconeLift_isColimit _ D c hv hc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullCoconeLift_inclusion _ D c hv⟩

/-- 概要：元の局所対象圏は同じ濃度で全小 filtered 余極限を持つ。
方針：周囲の余極限の存在を元の全部分圏への持ち上げへ渡す。
規約：局所対象圏の accessibility を仮定しない。
使われ方：小 compact 生成表示を加えた accessibility の構成。 -/
lemma hasSmallKappaFilteredColimits {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (hends : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) := by
  intro K hK hκK D
  obtain ⟨c, hc⟩ := hC K (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι)
  obtain ⟨d, hd, _⟩ := hasColimit_of_compactEndpoints edges hends D c hc
  exact ⟨d, hd⟩

/-- 概要：同じ端点濃度で局所対象の包含は filtered 余極限を保つ。
方針：周囲から持ち上げた余極限と任意の元の内部余極限を全余錐同型で比較する。
規約：任意の指定された内部余極限余錐の保存を結論する。
使われ方：反射した生成対象の compact 性の移送。 -/
lemma inclusion_isKappaAccessibleFunctor {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (hends : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι := by
  intro K hK hκK D c hc
  obtain ⟨d, hd⟩ := hC K (D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι)
  obtain ⟨d', hd', hsame⟩ := hasColimit_of_compactEndpoints edges hends D d hd
  have himg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι d') :=
    hsame.symm ▸ hd
  exact himg.of_functorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso d' c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d' c hd' hc)).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
