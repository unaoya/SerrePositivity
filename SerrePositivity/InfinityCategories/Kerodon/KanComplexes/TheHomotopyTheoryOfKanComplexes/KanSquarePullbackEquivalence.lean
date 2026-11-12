module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationEquivalenceLifting

/-!
概要：Kan fibration 間の同値な可換正方形は、同じ底への pullback 比較を同値にする。
方針：底の同値を Kan fibration に沿って引き戻し、同じ全空間の同値から消去する。
規約：モデル構造の instance を仮定しない。
使われ方：二つの底の異なる境界固定 fiber の実際の比較。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 全空間と底が同値な同じ正方形の pullback への比較は同値。 -/
lemma kanSquarePullbackLift_isQCatEquivalence
    {E F B D : SSet.{u}} [KanComplex E] [KanComplex F] [KanComplex B] [KanComplex D]
    (s : E ⟶ B) (t : F ⟶ D) [Fibration t] (u : E ⟶ F) (v : B ⟶ D)
    (h : u ≫ t = s ≫ v) (hu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence u) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pullback.lift u s h) := by
  have hfst : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pullback.fst t v) := by
    have he := hv.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting t
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEquivalenceLifting_of_kanFibration t)
    have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (pullbackSymmetry t v)).isQCatEquivalence.comp
      he.isQCatEquivalence
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pullbackSymmetry t v).hom ≫ pullback.snd v t) at hh
    simpa only [pullbackSymmetry_hom_comp_snd] using hh
  apply hfst.cancel_right
  rw [pullback.lift_fst]
  exact hu

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
