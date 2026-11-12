module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.IntervalMaximum

/-!
概要：任意のパラメータの時刻と変形時刻の最大値を取り、両端と固定時刻を計算する。
方針：F1B の区間最大値に二つの時刻を入力する。
規約：第一時刻のパラメータを保つ。
使われ方：余錐の正方形の対角を上辺へ変形する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {P Q : SSet.{u}}

/-- 概要：指定された時刻と変形時刻の最大値。
方針：二つの時刻を区間最大値へ写す。
規約：第二時刻が変形時刻。使われ方：対角の変形の縦座標。 -/
def timeMaximumAlong (s : P ⟶ (Δ[1] : SSet.{u})) : P ⊗ (Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  lift (fst P Δ[1] ≫ s) (snd P Δ[1]) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum

/-- 概要：変形の始点は指定時刻そのもの。
方針：第二時刻零の最大値を使う。規約：全単体。使われ方：対角の回収。 -/
lemma timeMaximumAlong_zero (s : P ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₀ ≫ timeMaximumAlong s = s := by
  have h : SSet.ι₀ ≫ lift (fst P Δ[1] ≫ s) (snd P Δ[1]) = s ≫ SSet.ι₀ := rfl
  rw [timeMaximumAlong, ← Category.assoc, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_second_zero, Category.comp_id]

/-- 概要：変形の終点は時刻一に定値。
方針：第二時刻一の最大値を使う。規約：全単体。使われ方：上辺への到達。 -/
lemma timeMaximumAlong_one (s : P ⟶ (Δ[1] : SSet.{u})) :
    SSet.ι₁ ≫ timeMaximumAlong s = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  have h : SSet.ι₁ ≫ lift (fst P Δ[1] ≫ s) (snd P Δ[1]) = s ≫ SSet.ι₁ := rfl
  rw [timeMaximumAlong, ← Category.assoc, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_second_one, SSet.comp_const]

/-- 概要：時刻の族の前合成は最大値の変形と可換。
方針：二射影で入力の直積射を比較する。規約：全時間。使われ方：横端点の固定。 -/
lemma timeMaximumAlong_precomp (a : Q ⟶ P) (s : P ⟶ (Δ[1] : SSet.{u})) :
    (a ▷ (Δ[1] : SSet.{u})) ≫ timeMaximumAlong s = timeMaximumAlong (a ≫ s) := by
  rw [timeMaximumAlong, timeMaximumAlong, ← Category.assoc]
  congr 1

/-- 概要：指定時刻が零なら変形時刻を回収する。
方針：第一時刻零の最大値を使う。規約：全時間。使われ方：固定始点の境界。 -/
lemma timeMaximumAlong_const_zero :
    timeMaximumAlong (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : P ⟶ _) =
      snd P (Δ[1] : SSet.{u}) := by
  have h : lift (fst P Δ[1] ≫ SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (snd P Δ[1]) = snd P Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] := by
    rw [SSet.comp_const]
    rfl
  rw [timeMaximumAlong, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_first_zero, Category.comp_id]

/-- 概要：指定時刻が一なら最大値は全時間で一。
方針：第一時刻一の最大値を使う。規約：全時間。使われ方：固定終点の境界。 -/
lemma timeMaximumAlong_const_one :
    timeMaximumAlong (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : P ⟶ _) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  have h : lift (fst P Δ[1] ≫ SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (snd P Δ[1]) = snd P Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[1] := by
    rw [SSet.comp_const]
    rfl
  rw [timeMaximumAlong, h, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_first_one, SSet.comp_const]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
