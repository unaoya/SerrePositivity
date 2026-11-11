module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 複体間の left fibration の全ホーン持ち上げ性。
方針：最後以外は左ホーンの定義を使い、最後のホーンは辺の可逆性で充填する。
規約：Fibration は全ホーンの右持ち上げ性としてのみ用い、モデル構造の公理は使わない。
使われ方：Kerodon §4.4.2（Tag 019C）、§5.3.1（Tag 035D）、strict transport の制限の相対的な比較。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：Kan 複体間の left fibration は全てのホーンを持ち上げる。
方針：欠ける面が最後のときだけ Kan 性による可逆辺の外側ホーン充填を使う。
規約：一次ホーンでは標的の辺、高次では始域の最後の辺の可逆性を使う。
使われ方：Kerodon §4.4.2（Tag 019C）、相対関手空間の制限の全ホーン持ち上げ。 -/
lemma leftFibration_hasLiftingProperty_horn_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    (n : ℕ) (i : Fin (n + 2)) : HasLiftingProperty (horn (n + 1) i).ι q := by
  by_cases hi : i < Fin.last (n + 1)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
  · have hi' : i = Fin.last (n + 1) := le_antisymm (Fin.le_last i) (le_of_not_gt hi)
    subst i
    constructor
    intro a b sq
    cases n with
    | zero =>
      have : IsGroupoid (hoFunctor.obj Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid Y
      have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv b)) :=
        IsGroupoid.all_isIso (C := hoFunctor.obj Y) _
      obtain ⟨F, hF, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftHorn_one_last q a b sq hb
      exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }
    | succ n =>
      have : IsGroupoid (hoFunctor.obj X) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid X
      have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
          (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n))) :=
        IsGroupoid.all_isIso (C := hoFunctor.obj X) _
      obtain ⟨F, hF, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.innerFibration_lift_finalHorn q n a b sq.w he
      exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := hFq }

/-- 概要：Kan 複体間の left fibration の全ホーン持ち上げ性を Fibration に束縛する。
方針：ホーンごとの持ち上げ性を既存のホーン判定に渡す。
規約：弱同値やモデル構造の因子分解は使わない。
使われ方：Kerodon §5.3.1（Tag 035D）、相対内部 Hom のパラメーター付きの比較。 -/
@[kerodon 048H]
lemma leftFibration_fibration_of_kanComplex {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] : Fibration q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn q (leftFibration_hasLiftingProperty_horn_of_kanComplex q)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
