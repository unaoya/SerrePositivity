module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectionColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectiveAccessibility

/-!
概要：既存の条件付き局所置換反射から局所対象全部分圏の presentability を構成する。
方針：共通端点 compact 濃度より大きい accessibility 濃度を選び、反射した小生成族を使う。
規約：反射の存在を入力とする条件付き結果。無条件の accessibility とは区別する。
使われ方：局所置換の存在を供給する P-f からの消費。

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


/-- 概要：元の presentable 圏の小さい辺族には任意の下界を超える包含の保存濃度がある。
方針：既存の共通端点 compact 濃度と filtered 閉性を使う。
規約：局所対象圏の accessibility や反射性は仮定しない。
使われ方：反射した生成対象の compact 性の濃度調整。 -/
lemma exists_regular_inclusion_accessibilityCardinal
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (Set.range edges)).ι := by
  obtain ⟨μ, hμ, hσ, hends⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_compactEndpoints hC edges σ
  have hc := hC.hasSmallColimits.hasSmallKappaFilteredColimits μ
  exact ⟨μ, hμ, hσ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasSmallKappaFilteredColimits edges hc hends,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.inclusion_isKappaAccessibleFunctor edges hc hends⟩

/-- 概要：既存の局所対象反射を入力に取ると元の局所対象全部分圏は accessible。
方針：共通端点濃度を超える周囲の小生成濃度を選び、同じ反射生成表示を構成する。
規約：小さい辺族と元の全部分圏を使用し、反射の存在は入力のままにする。
使われ方：条件付き presentability の accessibility 成分。 -/
lemma isAccessible_of_reflection {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {I : Type u} (edges : I → C _⦋1⦌)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) := by
  obtain ⟨μ, _hμ, _, hends⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_compactEndpoints hC edges Cardinal.aleph0
  obtain ⟨κ, hμκ, hκC⟩ := hC.isAccessible.exists_larger μ
  obtain ⟨r⟩ := hr
  have hendsκ : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 1 (edges i)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (C.δ 0 (edges i)) :=
    fun i ↦ ⟨(hends i).1.of_le hμκ.le, (hends i).2.of_le hμκ.le⟩
  exact ⟨κ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflectiveSubcategory_isKappaAccessible
    (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalObject_iff_of_vertexIso (Set.range edges) e) r hκC hC.hasSmallColimits
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.inclusion_isKappaAccessibleFunctor edges
      (hC.hasSmallColimits.hasSmallKappaFilteredColimits κ) hendsκ)⟩

/-- 概要：既存の条件付き反射を持つ局所対象全部分圏は presentable。
方針：同じ反射からの accessibility と全小余極限を合わせる。
規約：元の局所対象の定義を使用する。
使われ方：局所置換の構成からの presentability の主公開界面。 -/
lemma isPresentable_of_reflection {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {I : Type u} (edges : I → C _⦋1⦌)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsReflectiveSubcategory C (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges))) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) :=
  ⟨isAccessible_of_reflection hC edges hr,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasSmallColimits_of_reflection edges hC.hasSmallColimits hr⟩

/-- 概要：各対象の元の局所置換の存在から局所対象圏の presentability が従う。
方針：N の既存の条件付き反射をそのまま主公開界面へ渡す。
規約：局所置換の存在以外の生成性や accessibility を追加入力にしない。
使われ方：P-f の局所置換の存在からの直接の接続。 -/
lemma isPresentable_of_localReplacements {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) {I : Type u} (edges : I → C _⦋1⦌)
    (hreplace : ∀ x : C _⦋0⦌, ∃ (y : C _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj C) x y),
      e.edge ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (Set.range edges) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (Set.range edges) y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.Definition.Category edges) :=
  isPresentable_of_reflection hC edges
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements (Set.range edges) hreplace)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
