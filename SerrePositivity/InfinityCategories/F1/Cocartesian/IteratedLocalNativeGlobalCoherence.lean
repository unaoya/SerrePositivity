module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeGlobalNativeTransportCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IteratedLocalNativeCoherence

/-!
概要：既存の局所結合比較を元の全 Hom に戻すと、導出した三辺の第一因子そのもの。
方針：同じ二重底変換と三端点の回収で、元の二因子の指定値を貼り合わせる。
規約：既存の局所結合比較・指定因子・元の全 Hom 作用を保持する。
使われ方：元の三辺の等式を既存の局所自然性の指定値へ移す。
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

/-- 元の全 Hom 上の局所結合比較を表す、同じ指定二因子の合成。 -/
def cocartesianBaseChangeGlobalNativeComparisonIso :
    FunctorIso (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).targetMap
      (cocartesianBaseChangeGlobalNativeTransportPostIso l k p q).targetMap :=
  (cocartesianBaseChangeGlobalTransportCompositionIso l k p q).symm ≪≫
    cocartesianBaseChangeGlobalNativeTransportPostIso l k p q

/-- 既存の局所結合比較の前合成は、同じ元の全 Hom 上の指定二因子の合成に一致する。 -/
lemma cocartesianIteratedLocalHomComparison_nativeIso_originalHom_heq :
    HEq ((cocartesianIteratedLocalHomComparison_nativeIso l k p q).precomp
      (cocartesianDoubleBaseChangeHomAction l k p q))
      (cocartesianBaseChangeGlobalNativeComparisonIso l k p q) := by
  have h₁ := functorIsoOfEq_precomp_heq
    (cocartesianIteratedLocalNativeCompositeIso l k p q)
    (cocartesianIteratedLocalNativeComposite_source l k p q)
    (cocartesianIteratedLocalNativeComposite_target l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
  have h₂ := functorIso_precomp_inverse_paste_heq
    (cocartesianIteratedLocalNativeCompositionIso l k p q)
    (cocartesianIteratedLocalNativeNormalizedTransportFactorIso l k p q)
    (cocartesianDoubleBaseChangeHomAction l k p q)
    (cocartesianBaseChangeGlobalTransportCompositionIso l k p q)
    (cocartesianBaseChangeGlobalNativeTransportPostIso l k p q)
    (cocartesianBaseChangeGlobalComposition_native_source l k p q)
    (cocartesianBaseChangeGlobalComposition_native_target l k p q)
    (cocartesianBaseChangeGlobalNativeTransport_native_target l k p q)
    (cocartesianBaseChangeGlobalComposition_native_heq l k p q)
    (cocartesianBaseChangeGlobalNativeTransport_native_heq l k p q)
  exact HEq.trans h₁ h₂

end SerrePositivity.InfinityCategories
