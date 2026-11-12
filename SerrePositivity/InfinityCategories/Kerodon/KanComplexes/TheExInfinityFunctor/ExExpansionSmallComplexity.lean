module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingNondegenerate

/-!
# 閾値未満の単体の拡張

概要：複雑度が拡張の閾値未満なら、その拡張は通常の退化に一致する。
方針：固定点の式を挿入して Moss Lemma 26 (6) を適用する。
規約：Moss 2020 Lemma 29 の後ろの面の退化性。
使われ方：指定面の一意性と pairing の正則性。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：小さい複雑度を持つ単体の大きい閾値での拡張は通常の退化である。
方針：切断後の拡張退化が通常の退化に一致する式を前合成する。
規約：Moss 2020 Lemma 26 (6)、Lemma 29。
使われ方：閾値を下げられる後ろの面の退化性。
-/
theorem exExpansion_eq_degeneracy_of_complexity_lt (X : SSet.{u}) (n : ℕ)
    (h k : Fin (n + 1)) (hhk : h < k) (s : (SSet.ex.obj X) _⦋n⦌)
    (hs : s ∈ exComplexity X ⦋n⦌ h) :
    exExpansion X n k s = (SSet.ex.obj X).σ k s := by
  apply ULift.ext
  change subdivisionDegeneracyAt n k ≫ s.down =
    SimplexCategory.sd.map (SimplexCategory.σ k) ≫ s.down
  change subdivisionCutAt ⦋n⦌ h ≫ s.down = s.down at hs
  calc
    _ = subdivisionDegeneracyAt n k ≫ (subdivisionCutAt ⦋n⦌ h ≫ s.down) := by rw [hs]
    _ = (subdivisionDegeneracyAt n k ≫ subdivisionCutAt ⦋n⦌ h) ≫ s.down :=
      (Category.assoc _ _ _).symm
    _ = (SimplexCategory.sd.map (SimplexCategory.σ k) ≫ subdivisionCutAt ⦋n⦌ h) ≫ s.down :=
      congrArg (fun f => f ≫ s.down) (subdivisionDegeneracyAt_cut_lt n h k hhk)
    _ = _ := by rw [Category.assoc, hs]

/--
概要：小さい複雑度の単体の大きい閾値での拡張は退化している。
方針：通常の退化による表示を使う。
規約：Moss 2020 Lemma 29。
使われ方：非退化な単体に等しい後ろの面は最小閾値を保つこと。
-/
theorem exExpansion_degenerate_of_complexity_lt (X : SSet.{u}) (n : ℕ)
    (h k : Fin (n + 1)) (hhk : h < k) (s : (SSet.ex.obj X) _⦋n⦌)
    (hs : s ∈ exComplexity X ⦋n⦌ h) :
    exExpansion X n k s ∈ (SSet.ex.obj X).degenerate (n + 1) := by
  rw [exExpansion_eq_degeneracy_of_complexity_lt X n h k hhk s hs]
  exact (SSet.ex.obj X).σ_mem_degenerate _ _

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
