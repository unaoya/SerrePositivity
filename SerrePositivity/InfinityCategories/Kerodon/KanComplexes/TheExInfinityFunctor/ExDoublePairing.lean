module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingStep
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionDoubleDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# 二重の pairing 候補の退化性

概要：最小複雑度による次元上昇を二度適用すると退化単体となる。
方針：複雑度の保存と二重の拡張退化の式を組み合わせる。
規約：Moss 2020 Lemma 28 と Lemma 26 (7)。
使われ方：非退化な対応先の元は型 II であること。

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
概要：pairing 候補を二度適用した単体は、特定の通常の退化で表せる。
方針：最小閾値が変わらないことと拡張退化の合成則を使う。
規約：Moss 2020 Lemma 28 の証明で使う式。全単体について成り立つ。
使われ方：対応先が非退化なら元は他の対応先ではないこと。
-/
theorem exPairingStep_double (X : SSet.{u}) (n : ℕ) (s : (SSet.ex.obj X) _⦋n⦌) :
    exPairingStep X (n + 1) (exPairingStep X n s) =
      (SSet.ex.obj X).σ (exComplexityLevel X ⦋n⦌ s).succ (exPairingStep X n s) := by
  change exExpansion X (n + 1) (exComplexityLevel X ⦋n + 1⦌ (exPairingStep X n s))
    (exPairingStep X n s) = _
  rw [exPairingStep_complexityLevel]
  apply ULift.ext
  change subdivisionDegeneracyAt (n + 1) (exComplexityLevel X ⦋n⦌ s).castSucc ≫
      (subdivisionDegeneracyAt n (exComplexityLevel X ⦋n⦌ s) ≫ s.down) =
    SimplexCategory.sd.map (SimplexCategory.σ (exComplexityLevel X ⦋n⦌ s).succ) ≫
      (subdivisionDegeneracyAt n (exComplexityLevel X ⦋n⦌ s) ≫ s.down)
  rw [← Category.assoc, subdivisionDegeneracyAt_double, Category.assoc]

/--
概要：pairing 候補を二度適用した単体は退化している。
方針：明示した通常の退化の表示を使う。
規約：Moss 2020 Lemma 28 の退化性の部分。
使われ方：型 I・型 II の分割の検証。
-/
theorem exPairingStep_double_degenerate (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) :
    exPairingStep X (n + 1) (exPairingStep X n s) ∈ (SSet.ex.obj X).degenerate (n + 2) := by
  rw [exPairingStep_double]
  exact (SSet.ex.obj X).σ_mem_degenerate _ _

/--
概要：pairing 候補の像が非退化なら、その元は一つ前の pairing 候補の像ではない。
方針：前段の像であれば二重適用が退化することと矛盾する。
規約：Moss 2020 Lemma 28。非退化な型 I の元は型 II であるという部分の核。
使われ方：regular pairing の型 I と型 II の互いに素なこと。
-/
theorem exPairingStep_notMem_range_of_nonDegenerate (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n + 1⦌)
    (hs : exPairingStep X (n + 1) s ∈ (SSet.ex.obj X).nonDegenerate (n + 2)) :
    s ∉ Set.range (exPairingStep X n) := by
  rintro ⟨t, rfl⟩
  exact ((SSet.ex.obj X).mem_nonDegenerate_iff_notMem_degenerate _).mp hs
    (exPairingStep_double_degenerate X n t)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
