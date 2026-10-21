module

public import SerrePositivity.InfinityCategories.F1.CocartesianIsoTransportNativeHomOne
public import SerrePositivity.InfinityCategories.F1.CocartesianRawHomCongr
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeHomEvaluation

/-!
概要：全局所比較の raw な共役の core は、既存の元の core Hom 同型そのもの。
方針：全次数と全パラメーターで同じ前後合成を評価し、射の一致を得る。
規約：大域 Hom からの制限像に限定しない。
使われ方：既存の底制限一致と同じ結合 Hom 輸送の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 全局所比較の共役作用は、既存の元の core Hom の指定結合同型そのもの。 -/
lemma cocartesianIsoTransportNativeHomMap_eq :
    cocartesianIsoTransportNativeHomMap l k p q =
      (cocartesianBaseChangeNativeHomIso l k p q).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  have h := cocartesianRawHomCongr_apply
    (cocartesianBaseChangeIsoTransportObject l k p).comparison
    (cocartesianBaseChangeIsoTransportObject l k q).comparison s.val α x
  exact h.trans (cocartesianBaseChangeNativeHomIso_apply l k p q s α x).symm

end SerrePositivity.InfinityCategories
