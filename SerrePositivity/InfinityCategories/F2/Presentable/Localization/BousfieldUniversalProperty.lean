module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.BousfieldReflection
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveLocalization
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointAllColimitPreservation

/-!
概要：構成した Bousfield 反射の小余極限保存性・accessibility と反転辺に関する普遍性。
方針：同じ反射データの随伴と、既存の全標的での前合成同値を使用する。
規約：反転辺と強飽和生成閉包の同定は BousfieldSaturation で接続する。
使われ方：HTT 5.5.4.15(2) と f4 の公開同定への接続。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization

/-- 同じ構成した局所化関手は、元の指定小余極限をすべて保存する。 -/
lemma bousfieldLocalizationFunctor_preservesSmallColimits
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    PreservesSmallColimits (bousfieldLocalizationFunctor hC edges) :=
  adjunction_preservesSmallColimits (bousfieldReflection hC edges).adjunction

/-- 同じ局所化関手は accessible であり、濃度は追加の入力ではない。 -/
lemma bousfieldLocalizationFunctor_isAccessible
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    IsAccessibleFunctor (bousfieldLocalizationFunctor hC edges) :=
  ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0,
    (bousfieldLocalizationFunctor_preservesSmallColimits hC edges).isKappaAccessibleFunctor _⟩

/-- 構成した同じ全関手は、自身の反転辺について全標的での局所化普遍性を持つ。 -/
lemma bousfieldLocalizationFunctor_isLocalization_invertedEdges
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsPresentable C)
    {I : Type u} (edges : I → C _⦋1⦌) :
    IsLocalization (bousfieldLocalizationFunctor hC edges)
      (invertedEdges (bousfieldLocalizationFunctor hC edges)) :=
  (bousfieldReflection hC edges).isLocalization

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
