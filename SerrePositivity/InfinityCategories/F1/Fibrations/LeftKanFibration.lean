module

public import SerrePositivity.InfinityCategories.Core.KanFibrationTools

/-!
概要：Kan 複体間の left fibration の全ホーン持ち上げ性。
方針：最後以外は左ホーンの定義を使い、最後のホーンは辺の可逆性で充填する。
規約：Fibration は全ホーンの右持ち上げ性としてのみ用い、モデル構造の公理は使わない。
使われ方：Kerodon §4.4.2、§5.3.1、strict transport の制限の相対的な比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：Kan 複体間の left fibration は全てのホーンを持ち上げる。
方針：欠ける面が最後のときだけ Kan 性による可逆辺の外側ホーン充填を使う。
規約：一次ホーンでは標的の辺、高次では始域の最後の辺の可逆性を使う。
使われ方：Kerodon §4.4.2、相対関手空間の制限の全ホーン持ち上げ。 -/
lemma leftFibration_hasLiftingProperty_horn_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [LeftFibration q]
    (n : ℕ) (i : Fin (n + 2)) : HasLiftingProperty (horn (n + 1) i).ι q := by
  by_cases hi : i < Fin.last (n + 1)
  · exact LeftFibration.mem (p := q) _ (leftHornInclusions.intro i hi)
  · have hi' : i = Fin.last (n + 1) := le_antisymm (Fin.le_last i) (le_of_not_gt hi)
    subst i
    constructor
    intro a b sq
    cases n with
    | zero =>
      have : IsGroupoid (hoFunctor.obj Y) := kanComplex_ho_isGroupoid Y
      have hb : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv b)) :=
        IsGroupoid.all_isIso (C := hoFunctor.obj Y) _
      obtain ⟨F, hF, hFq⟩ := leftFibration_liftHorn_one_last q a b sq hb
      exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }
    | succ n =>
      have : IsGroupoid (hoFunctor.obj X) := kanComplex_ho_isGroupoid X
      have he : IsInvertibleEdge (edgeOfSimplex
          (a.app (Opposite.op ⦋1⦌) (finalHornEdge n))) :=
        IsGroupoid.all_isIso (C := hoFunctor.obj X) _
      obtain ⟨F, hF, hFq⟩ := innerFibration_lift_finalHorn q n a b sq.w he
      exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }

/-- 概要：Kan 複体間の left fibration の全ホーン持ち上げ性を Fibration に束縛する。
方針：ホーンごとの持ち上げ性を既存のホーン判定に渡す。
規約：弱同値やモデル構造の因子分解は使わない。
使われ方：Kerodon §5.3.1、相対内部 Hom のパラメーター付きの比較。 -/
lemma leftFibration_fibration_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [LeftFibration q] : Fibration q :=
  fibration_of_hasLiftingProperty_horn q (leftFibration_hasLiftingProperty_horn_of_kanComplex q)

end SerrePositivity.InfinityCategories
