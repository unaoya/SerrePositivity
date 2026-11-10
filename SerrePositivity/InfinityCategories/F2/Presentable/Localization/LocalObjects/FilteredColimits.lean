module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects.FilteredClosure
public import SerrePositivity.InfinityCategories.F2.Ind.FullCoconeLift
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Core.ColimitDiagramIso

/-!
概要：元の局所対象全部分圏の filtered 余極限を周囲と同じ余錐から構成する。
方針：閉性で余極限頂点の局所性を得て全部分圏へ持ち上げ、全余錐比較で包含の保存を示す。
規約：局所置換反射を仮定しない。
使われ方：共通の正則濃度での局所対象包含の accessibility。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
open HomotopyLimits

/-- 概要：共通 compact 端点の濃度で元の局所対象図式は内部の余極限を持つ。
方針：周囲の同じ余極限余錐を閉性により持ち上げる。
規約：同じ全図式と元の全部分圏を使用する。
使われ方：局所対象圏の filtered 余完備性。 -/
lemma hasColimit_of_compactEndpoints {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hends : ∀ i, Compact.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      Compact.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i)))
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Category edges)
    (c : JoinCocone (D ≫ (localObjectsSubcomplex (Set.range edges)).ι))
    (hc : IsColimitCone c) :
    ∃ d : JoinCocone D, IsColimitCone d ∧
      mapJoinCocone (localObjectsSubcomplex (Set.range edges)).ι d = c := by
  have hv : IsLocalObject (Set.range edges) c.vertex :=
    isLocalObject_colimit_of_compactEndpoints edges hends _ c hc
      (fun k ↦ fullSubcomplexOnVertices_vertex (D.app _ (ULift.up k)))
  exact ⟨Ind.fullCoconeLift _ D c hv, Ind.fullCoconeLift_isColimit _ D c hv hc,
    Ind.fullCoconeLift_inclusion _ D c hv⟩

/-- 概要：元の局所対象圏は同じ濃度で全小 filtered 余極限を持つ。
方針：周囲の余極限の存在を元の全部分圏への持ち上げへ渡す。
規約：局所対象圏の accessibility を仮定しない。
使われ方：小 compact 生成表示を加えた accessibility の構成。 -/
lemma hasSmallKappaFilteredColimits {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (hends : ∀ i, Compact.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      Compact.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i))) :
    Ind.HasSmallKappaFilteredColimits κ (Category edges) := by
  intro K hK hκK D
  obtain ⟨c, hc⟩ := hC K (D ≫ (localObjectsSubcomplex (Set.range edges)).ι)
  obtain ⟨d, hd, _⟩ := hasColimit_of_compactEndpoints edges hends D c hc
  exact ⟨d, hd⟩

/-- 概要：同じ端点濃度で局所対象の包含は filtered 余極限を保つ。
方針：周囲から持ち上げた余極限と任意の元の内部余極限を全余錐同型で比較する。
規約：任意の指定された内部余極限余錐の保存を結論する。
使われ方：反射した生成対象の compact 性の移送。 -/
lemma inclusion_isKappaAccessibleFunctor {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (hends : ∀ i, Compact.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      Compact.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (localObjectsSubcomplex (Set.range edges)).ι := by
  intro K hK hκK D c hc
  obtain ⟨d, hd⟩ := hC K (D ≫ (localObjectsSubcomplex (Set.range edges)).ι)
  obtain ⟨d', hd', hsame⟩ := hasColimit_of_compactEndpoints edges hends D d hd
  have himg : IsColimitCone (mapJoinCocone (localObjectsSubcomplex (Set.range edges)).ι d') :=
    hsame.symm ▸ hd
  exact himg.of_functorIso
    ((coconeFunctorIsoOfVertexIso d' c (colimitConeIso d' c hd' hc)).postcomp
      (localObjectsSubcomplex (Set.range edges)).ι)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization.LocalObjects
