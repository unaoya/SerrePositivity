module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMinimum

/-!
概要：任意のパラメータの時刻と変形時刻の最小値を取り、両端と固定時刻を計算する。
方針：区間最小値に二つの時刻を入力する。
規約：第一時刻のパラメータを保つ。
使われ方：錐の正方形の下辺を対角へ変形する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable {P Q : SSet.{u}}

/-- 概要：指定された時刻と変形時刻の最小値。
方針：二つの時刻を区間最小値へ写す。
規約：第二時刻が変形時刻。使われ方：対角の変形の縦座標。 -/
def timeMinimumAlong (s : P ⟶ (Δ[1] : SSet.{u})) : P ⊗ (Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  lift (fst P Δ[1] ≫ s) (snd P Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum

/-- 概要：変形の始点は時刻零に定値。
方針：第二時刻零の最小値を使う。規約：全単体。使われ方：下辺の回収。 -/
lemma timeMinimumAlong_zero (s : P ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₀ ≫ timeMinimumAlong s = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have h : SSet.ι₀ ≫ lift (fst P Δ[1] ≫ s) (snd P Δ[1]) = s ≫ SSet.ι₀ := rfl
  rw [timeMinimumAlong, ← Category.assoc, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_second_zero, SSet.comp_const]

/-- 概要：変形の終点は元の指定時刻。
方針：第二時刻一の最小値を使う。規約：全単体。使われ方：対角への到達。 -/
lemma timeMinimumAlong_one (s : P ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₁ ≫ timeMinimumAlong s = s := by
  have h : SSet.ι₁ ≫ lift (fst P Δ[1] ≫ s) (snd P Δ[1]) = s ≫ SSet.ι₁ := rfl
  rw [timeMinimumAlong, ← Category.assoc, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_second_one, Category.comp_id]

/-- 概要：時刻の族の前合成は最小値の変形と可換。
方針：二射影で入力の直積射を比較する。規約：全時間。使われ方：横端点の固定。 -/
lemma timeMinimumAlong_precomp (a : Q ⟶ P) (s : P ⟶ (Δ[1] : SSet.{u})) :
    (a ▷ (Δ[1] : SSet.{u})) ≫ timeMinimumAlong s = timeMinimumAlong (a ≫ s) := by
  rw [timeMinimumAlong, timeMinimumAlong, ← Category.assoc]
  congr 1

/-- 概要：指定時刻が零なら全時間で零。
方針：第一時刻零の最小値を使う。規約：全時間。使われ方：固定始点の境界。 -/
lemma timeMinimumAlong_const_zero :
    timeMinimumAlong (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : P ⟶ _) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have h : lift (fst P Δ[1] ≫ SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (snd P Δ[1]) = snd P Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
    rw [SSet.comp_const]
    rfl
  rw [timeMinimumAlong, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_first_zero, SSet.comp_const]

/-- 概要：指定時刻が一なら変形時刻を回収する。
方針：第一時刻一の最小値を使う。規約：全時間。使われ方：固定終点の境界。 -/
lemma timeMinimumAlong_const_one :
    timeMinimumAlong (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : P ⟶ _) =
      snd P (Δ[1] : SSet.{u}) := by
  have h : lift (fst P Δ[1] ≫ SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (snd P Δ[1]) = snd P Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
    rw [SSet.comp_const]
    rfl
  rw [timeMinimumAlong, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMinimum_first_one, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
