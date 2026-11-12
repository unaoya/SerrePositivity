module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.NerveHornLift
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：quasicategory 値 weighted nerve の射影は inner fibration。
方針：元の最後の係数ホーンを quasicategory の inner horn として充填する。
規約：Kan 性は仮定せず、全ての内ホーンを同じ相対係数の構成で持ち上げる。
使われ方：Cat∞ 値 unstraightening の cocartesian fibration を構成する初段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 最後の係数が quasicategory なら、指定した元の相対 inner horn は充填できる。 -/
lemma exists_weightedNerve_innerHorn_lift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    [Quasicategory (F.obj (σ.obj (Fin.last (n + 1))))] (k : Fin (n + 2))
    (h0 : 0 < k) (hn : k < Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      (horn (n + 1) k).ι ≫ H = a ∧ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = SSet.yonedaEquiv.symm σ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.exists_weightedNerveHorn_lift_of_coefficient_filler F σ k (ne_of_lt hn) a ha
  obtain ⟨H, hH⟩ := Quasicategory.hornFilling h0 hn (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha)
  exact ⟨H, hH.symm⟩

/-- quasicategory 値の元の weighted nerve の射影は inner fibration。 -/
instance weightedNerveProjection_innerFibration {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) where
  mem := by
    intro A B i hi
    cases hi with
    | @intro n k h0 hn =>
      constructor
      intro a b sq
      let σ := SSet.yonedaEquiv b
      have hb : SSet.yonedaEquiv.symm σ = b := SSet.yonedaEquiv.symm_apply_apply _
      have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
          (horn (n + 2) k).ι ≫ SSet.yonedaEquiv.symm σ := by rw [hb]; exact sq.w
      obtain ⟨H, hH, hHp⟩ := exists_weightedNerve_innerHorn_lift F σ k h0 hn a ha
      exact CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := hHp.trans hb }

/-- 元の quasicategory 値 weighted nerve の全空間も quasicategory。 -/
instance weightedNerve_quasicategory_of_quasicategory {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F)

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
