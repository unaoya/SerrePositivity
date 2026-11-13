module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.BousfieldReflection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation

/-!
概要：構成した Bousfield 反射の小余極限保存性・accessibility と反転辺に関する普遍性。
方針：同じ反射データの随伴と、既存の全標的での前合成同値を使用する。
規約：反転辺と強飽和生成閉包の同定は BousfieldSaturation で接続する。
使われ方：HTT 5.5.4.15(2) と f4 の公開同定への接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 同じ構成した局所化関手は、元の指定小余極限をすべて保存する。 -/
lemma bousfieldLocalizationFunctor_preservesSmallColimits
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldReflection hC edges).adjunction

/-- 同じ局所化関手は accessible であり、濃度は追加の入力ではない。 -/
lemma bousfieldLocalizationFunctor_isAccessible
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges) :=
  ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0,
    (bousfieldLocalizationFunctor_preservesSmallColimits hC edges).isKappaAccessibleFunctor _⟩

/-- 構成した同じ全関手は、自身の反転辺について全標的での局所化普遍性を持つ。 -/
lemma bousfieldLocalizationFunctor_isLocalization_invertedEdges
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor hC edges)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldReflection hC edges).isLocalization

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Lemma 5.5" (partial := direction) "仮定：表示可能準圏と、小さい辺族で強飽和生成された辺の類（原典の小生成からの向きと一致）。結論：元の局所対象圏は表示可能で、強飽和生成閉包に沿う反射が余極限を保ち、同じ辺の反転を表す（原典の小生成から局所化への向き）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.bousfieldLocalizationFunctor_preservesSmallColimits
