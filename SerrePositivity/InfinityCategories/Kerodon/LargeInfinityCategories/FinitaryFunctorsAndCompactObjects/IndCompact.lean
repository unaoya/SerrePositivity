module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.FullCompactReflection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.YonedaCompact
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaColimits

/-!
概要：元の Indκ 内の表現可能前層は、元の全共変 Hom による意味で κ-compact。
方針：元の全部分包含の全 Hom 比較と、同じ κ-filtered 余極限の保存を合成する。
規約：元の Yoneda 因子化を厳密に保持。Ind の単一 filtered 表示は使わない。
使われ方：HTT 5.3.5.5、compact な Ind 対象と Yoneda retract 閉包の比較。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の Ind 包含は、前層内の同じ対象の κ-compact 性を反映する。 -/
lemma ind_isKappaCompact_of_presheaf (κ : Cardinal.{u}) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C).app _ x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_fullSubcomplex_of_image κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C) x
    (fun _ _ _ D c hc ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_inclusion_isColimit κ D c hc) hx

/-- 元の Indκ 内へ因子化した同じ Yoneda 像は κ-compact。 -/
lemma indYoneda_isKappaCompact (κ : Cardinal.{u}) (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up y)) := by
  apply ind_isKappaCompact_of_presheaf
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C).app _ (ULift.up y))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.yonedaInfinityMap_isKappaCompact κ y

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
