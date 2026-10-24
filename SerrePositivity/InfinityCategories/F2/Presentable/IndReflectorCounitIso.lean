module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndReflectorUnitCounit
public import SerrePositivity.InfinityCategories.F2.Presentable.CanonicalKanRestrictionIso

/-!
概要：専用反映候補の余単位の可逆性。
方針：候補の制限と恒等関手の密度保存を使い、Yoneda 制限で可逆性を反映する。
規約：指定された逆単位を延長する余単位そのものを判定する。
使われ方：反映の三角恒等式と局所対象の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]

variable {L : PresheafInfinity C ⟶ IndInfinity κ C}
    (β : SSet.Homotopy (indYoneda κ C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (indYoneda κ C) L β)
include β hβ

/-- 概要：包含後に表示した同じ Yoneda 単位も可逆。
方針：元の可逆単位の後合成と端点の輸送を使う。
規約：指定された元の h Fun の射を保持する。
使われ方：左三角合成の Yoneda 制限の可逆性。 -/
lemma indReflectorYonedaUnit_isIso : IsIso (indReflectorYonedaUnit β) := by
  have := presheafYonedaLeftKan_unit_isIso β hβ
  dsimp only [indReflectorYonedaUnit, F1B.kanFunctorHomCongr, Iso.homCongr_apply,
    Iso.homCongr, Equiv.coe_fn_mk]
  infer_instance

/-- 概要：指定逆単位を延長する余単位は可逆。
方針：二つの関手が保つ密度と制限の可逆性を使う。
規約：各点の可逆性を独立な仮定にしない。
使われ方：反映の局所対象の回収。 -/
lemma indReflector_counit_isIso
    (ε : FunctorHom (indInclusionPresheaf κ C ≫ L) (𝟙 (IndInfinity κ C)))
    (hε : (hoFunctor.map ((pre (indYoneda κ C)).app
      (IndInfinity κ C))).toFunctor.map ε =
        indReflectorRestrictionYonedaInverse β hβ) : IsIso ε := by
  apply functorHom_isIso_of_canonicalRestriction (indYoneda κ C)
    (indReflectorRestriction_canonicalColimits β hβ) indReflectorIdentity_canonicalColimits ε
  rw [hε]
  have := indReflectorRestrictionYonedaUnit_isIso β hβ
  dsimp only [indReflectorRestrictionYonedaInverse]
  infer_instance

end SerrePositivity.InfinityCategories.F2.Presentable
