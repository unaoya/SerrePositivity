module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorUnitCounit
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
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]

/-- 概要：P_Σ 恒等関手の元の標準密度余錐は余極限。
方針：既存の元の密度余錐の普遍性を全標準余錐へ戻す。
規約：同じ恒等関手を使う。
使われ方：余単位の可逆性の反映。 -/
lemma sigmaIdentity_canonicalColimits (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C) (𝟙 _) v) := by
  apply (sigmaCanonicalColimits_iff_densityImages (𝟙 (SigmaPresheafInfinity C))).mpr
    (fun w ↦ ?_) v
  exact (F2.isColimitCone_iff_of_cocone_val_eq (sigmaVertexDensityCocone w)
    (mapJoinCocone (𝟙 _) (sigmaVertexDensityCocone w)) (by simp [mapJoinCocone])).mp
      (sigmaVertexDensityCocone_isColimit w)

variable {L : PresheafInfinity C ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β)
include β hβ

/-- 概要：包含後に表示した同じ Yoneda 単位も可逆。
方針：元の可逆単位の後合成と端点の輸送を使う。
規約：指定された元の h Fun の射を保持する。
使われ方：左三角合成の Yoneda 制限の可逆性。 -/
lemma sigmaReflectorYonedaUnit_isIso : IsIso (sigmaReflectorYonedaUnit β) := by
  have := sigmaReflectorLeftKan_unit_isIso β hβ
  dsimp only [sigmaReflectorYonedaUnit, F1B.kanFunctorHomCongr, Iso.homCongr_apply,
    Iso.homCongr, Equiv.coe_fn_mk]
  infer_instance

/-- 概要：指定逆単位を延長する余単位は可逆。
方針：二つの関手が保つ密度と制限の可逆性を使う。
規約：各点の可逆性を独立な仮定にしない。
使われ方：反映の局所対象の回収。 -/
lemma sigmaReflector_counit_isIso
    (ε : FunctorHom (sigmaPresheafInfinityInclusion C ≫ L) (𝟙 (SigmaPresheafInfinity C)))
    (hε : (hoFunctor.map ((pre (sigmaYonedaInfinityMap C)).app
      (SigmaPresheafInfinity C))).toFunctor.map ε =
        sigmaReflectorRestrictionYonedaInverse β hβ) : IsIso ε := by
  apply functorHom_isIso_of_canonicalRestriction (sigmaYonedaInfinityMap C)
    (sigmaReflectorRestriction_canonicalColimits β hβ) sigmaIdentity_canonicalColimits ε
  rw [hε]
  have := sigmaReflectorRestrictionYonedaUnit_isIso β hβ
  dsimp only [sigmaReflectorRestrictionYonedaInverse]
  infer_instance

end SerrePositivity.InfinityCategories.F2.Presentable
