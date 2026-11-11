module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# 通常の忠実平坦性から完全忠実平坦性

## 概要
忠実平坦な代数は任意のイデアルについて完全忠実平坦。
## 方針
平坦加群の高次 Tor 消滅と、通常の底変換による忠実平坦性を使う。
## 規約
完備性・有限生成性は不要。
## 使われ方
環同型による BS の包絡の係数環の照合。
-/

public noncomputable section
universe u
namespace SerrePositivity
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- 通常の忠実平坦な代数は、任意のイデアルについて完全忠実平坦である。 -/
theorem isCompletelyFaithfullyFlat_of_faithfullyFlat (I : Ideal R) [Module.FaithfullyFlat R S] :
    IsCompletelyFaithfullyFlat I S := by
  refine ⟨?_, inferInstance⟩
  intro N _ _ _
  apply (isConcentratedInDegreeZero_derivedTensor_iff S N).mpr
  intro i hi
  cases i with
  | zero => omega
  | succ i => exact torModule_subsingleton_of_flat S N i

end SerrePositivity
