module

public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceLiftingPullback
public import SerrePositivity.InfinityCategories.F1.KanModels.KanFibrationEquivalenceLifting

/-!
概要：Kan fibration 間の同値な可換正方形は、同じ底への pullback 比較を同値にする。
方針：底の同値を Kan fibration に沿って引き戻し、同じ全空間の同値から消去する。
規約：モデル構造の instance を仮定しない。
使われ方：二つの底の異なる境界固定 fiber の実際の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 全空間と底が同値な同じ正方形の pullback への比較は同値。 -/
lemma kanSquarePullbackLift_isQCatEquivalence
    {E F B D : SSet.{u}} [KanComplex E] [KanComplex F] [KanComplex B] [KanComplex D]
    (s : E ⟶ B) (t : F ⟶ D) [Fibration t] (u : E ⟶ F) (v : B ⟶ D)
    (h : u ≫ t = s ≫ v) (hu : IsQCatEquivalence u) (hv : IsQCatEquivalence v) :
    IsQCatEquivalence (pullback.lift u s h) := by
  have hfst : IsQCatEquivalence (pullback.fst t v) := by
    have he := hv.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting t
      (kanEquivalenceLifting_of_kanFibration t)
    have hh := (qCatEquivalenceOfIso (pullbackSymmetry t v)).isQCatEquivalence.comp
      he.isQCatEquivalence
    change IsQCatEquivalence ((pullbackSymmetry t v).hom ≫ pullback.snd v t) at hh
    simpa only [pullbackSymmetry_hom_comp_snd] using hh
  apply hfst.cancel_right
  rw [pullback.lift_fst]
  exact hu

end SerrePositivity.InfinityCategories
