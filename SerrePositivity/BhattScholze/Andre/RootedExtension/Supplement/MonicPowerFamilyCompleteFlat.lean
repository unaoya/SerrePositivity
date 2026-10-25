module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.MonicPowerFamilyCover
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.HomologicalAlgebra.Tor

/-! # B4-6：通常冪根添加環の完全忠実平坦性

具体的な自由・忠実平坦の結果を、既存Tor判定と剰余基底変更で接続する。
対象は未完備の通常環であり、perfectoid性や実完備化の保存は結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (n : ℕ) (σ R : Type u) [CommRing R]

/-- 通常冪根添加環は任意のイデアルに関して完全平坦。
既存Torの平坦な第1変数の消滅をそのまま使う。 -/
theorem monicPowerFamilyCover_isCompletelyFlat (c : σ → R) (hn : 0 < n) (I : Ideal R) :
    IsCompletelyFlat I (MonicPowerFamilyCover n σ R c) := by
  let := monicPowerFamilyCover_moduleFlat n σ R c hn
  intro N _ _ _
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact torModule_subsingleton_of_flat (R := R) (MonicPowerFamilyCover n σ R c) N i

/-- 通常冪根添加環は任意イデアルに関して完全忠実平坦。零環も含む。
ここでは通常の忠実平坦性を証明済みの具体的な環にだけ適用する。 -/
theorem monicPowerFamilyCover_isCompletelyFaithfullyFlat
    (c : σ → R) (hn : 0 < n) (I : Ideal R) :
    IsCompletelyFaithfullyFlat I (MonicPowerFamilyCover n σ R c) := by
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all n σ R c hn
  refine ⟨monicPowerFamilyCover_isCompletelyFlat n σ R c hn I, ?_⟩
  infer_instance

end SerrePositivity.BhattScholze
