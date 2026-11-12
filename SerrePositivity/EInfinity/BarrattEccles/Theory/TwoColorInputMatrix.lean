module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorInputComponents
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorWordCounts

/-!
# 実際の二色入力の誘導行列

HA 3.2.4.7 の自由比較のため、標準二色入力の誘導包含と余誘導射影を照合する。
部分群の外では行列成分が零であり、同じ成分の行列は標準の誘導・余誘導同型となる。
任意の入力複体の各整数次数で、既存の作用と指定包含・射影を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
attribute [local instance] Classical.propDecidable
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A) (m n : ℕ)

set_option maxHeartbeats 800000 in
-- 各次数の Rep の台と複体作用を同時に展開する照合に必要。
/-- 部分群の外の置換では、指定二色成分の自己行列が消える。 -/
lemma twoColorStandardInput_off_diagonal (i : ℤ)
    (g : ULift.{u} (Equiv.Perm (Fin (m + n))))
    (hg : g ∉ (twoColorPermutationHom.{u} m n).range)
    (x : (twoColorStandardInput X Y m n).X i) :
    ((twoColorStandardInputProjection X Y m n).f i).hom
      (((twoColorFullInput X Y m n).X i).ρ g
        (((twoColorStandardInputInclusion X Y m n).f i).hom x)) = 0 := by
  have hn : g.down • binaryTensorStandardPattern m n ≠ binaryTensorStandardPattern m n := by
    intro he
    exact hg ((binaryTensorStandard_mem_twoColor_iff m n g.down).mpr he)
  have hc := binaryTensorWordPermutation_component_ne X Y (m + n) g.down
    (binaryTensorStandardPattern m n) (binaryTensorStandardPattern m n) hn
  exact congrArg (fun f => (f.f i).hom x) hc

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 800000 in
-- 既知の入力の型を保ち、誘導表現の内部の不要な展開を避けて照合する。
/-- 指定した誘導包含と余誘導射影の合成は、各次数で標準の比較同型。 -/
lemma twoColorInducedInputInclusion_projection (i : ℤ) :
    letI : DecidablePred (fun g => g ∈ (twoColorPermutationHom.{u} m n).range) :=
      fun _ => Classical.propDecidable _
    finiteInductionInclusion (twoColorPermutationHom.{u} m n).range
        ((twoColorStandardInput X Y m n).X i) ((twoColorFullInput X Y m n).X i)
        ((twoColorStandardInputInclusion X Y m n).f i) ≫
      finiteCoinductionProjection (twoColorPermutationHom.{u} m n).range
        ((twoColorStandardInput X Y m n).X i) ((twoColorFullInput X Y m n).X i)
        ((twoColorStandardInputProjection X Y m n).f i) =
          (Rep.indCoindIso ((twoColorStandardInput X Y m n).X i)).hom := by
  have h := finiteInduction_projection_matrix (R := A)
    (G := ULift.{u} (Equiv.Perm (Fin (m + n)))) (twoColorPermutationHom.{u} m n).range
    ((twoColorStandardInput X Y m n).X i) ((twoColorFullInput X Y m n).X i)
    ((twoColorStandardInputInclusion X Y m n).f i)
    ((twoColorStandardInputProjection X Y m n).f i)
    (twoColorStandardInputInclusion_projection X Y m n i)
    (twoColorStandardInput_off_diagonal X Y m n i)
  exact h

end SerrePositivity.EInfinity.BarrattEccles
