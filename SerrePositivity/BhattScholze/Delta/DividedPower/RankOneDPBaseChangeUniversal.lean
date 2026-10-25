module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPTensorRelations

/-! # 任意係数への一元分冪代数の実テンソル基底変更

既存比較射の逆をlift'で具体的に構成する。係数環のねじれを制限しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- γ_n(b)をb^n⊗γ_n(1)へ送る実逆射。 -/
def rankOneDPBaseChangeInverse :
    DividedPowerAlgebra B B →ₐ[B] B ⊗[A] DividedPowerAlgebra A A :=
  DividedPowerAlgebra.lift' (f := fun nm ↦ rankOneDPTensorValue (A := A) nm.1 nm.2)
    rankOneDPTensorValue_zero rankOneDPTensorValue_smul
    rankOneDPTensorValue_mul rankOneDPTensorValue_add

/-- 逆射の全分冪生成元上の具体的な式。 -/
theorem rankOneDPBaseChangeInverse_dp (n : ℕ) (b : B) :
    rankOneDPBaseChangeInverse (A := A) (DividedPowerAlgebra.dp B n b) =
      rankOneDPTensorValue (A := A) n b := by
  rw [rankOneDPBaseChangeInverse, DividedPowerAlgebra.lift'_apply_dp]

/-- 逆射は標準生成元を指定された純テンソルへ送る。 -/
theorem rankOneDPBaseChangeInverse_dp_one (n : ℕ) :
    rankOneDPBaseChangeInverse (A := A) (DividedPowerAlgebra.dp B n (1 : B)) =
      (1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A) := by
  rw [rankOneDPBaseChangeInverse_dp, rankOneDPTensorValue, one_pow]

/-- 実比較射と実逆射の合成は、拡大後の分冪代数上の恒等射。 -/
theorem rankOneDPBaseChangeMap_comp_inverse :
    (rankOneDPBaseChangeMap (A := A) (B := B)).comp rankOneDPBaseChangeInverse =
      AlgHom.id B (DividedPowerAlgebra B B) := by
  apply DividedPowerAlgebra.algHom_ext
  intro n b
  change rankOneDPBaseChangeMap
    (rankOneDPBaseChangeInverse (DividedPowerAlgebra.dp B n b)) = DividedPowerAlgebra.dp B n b
  rw [rankOneDPBaseChangeInverse_dp, rankOneDPTensorValue,
    rankOneDPBaseChangeMap_tmul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one]
  simpa only [smul_eq_mul, mul_one, Algebra.smul_def] using
    (DividedPowerAlgebra.dp_smul (R := B) (r := b) (n := n) (m := (1 : B))).symm

/-- 実逆射と実比較射の合成は、実テンソル代数上の恒等射。 -/
theorem rankOneDPBaseChangeInverse_comp_map :
    (rankOneDPBaseChangeInverse (A := A) (B := B)).comp rankOneDPBaseChangeMap =
      AlgHom.id B (B ⊗[A] DividedPowerAlgebra A A) := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply DividedPowerAlgebra.algHom_ext
    intro n a
    change rankOneDPBaseChangeInverse
      (rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n a)) = _
    rw [rankOneDPBaseChangeMap_tmul, map_one, one_mul,
      DividedPowerAlgebra.map_apply_dp, rankOneDPBaseChangeInverse_dp]
    have ha : DividedPowerAlgebra.dp A n a = a ^ n • DividedPowerAlgebra.dp A n (1 : A) := by
      simpa only [smul_eq_mul, mul_one] using
        (DividedPowerAlgebra.dp_smul (R := A) (r := a) (n := n) (m := (1 : A)))
    change ((algebraMap A B a) ^ n) ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A) =
      (1 : B) ⊗ₜ[A] DividedPowerAlgebra.dp A n a
    rw [ha, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [Algebra.smul_def, mul_one, map_pow]

/-- 任意の可換係数環に対する、既存実比較射を順射とする代数同型。 -/
def rankOneDPBaseChangeUniversalEquiv :
    B ⊗[A] DividedPowerAlgebra A A ≃ₐ[B] DividedPowerAlgebra B B :=
  AlgEquiv.ofAlgHom rankOneDPBaseChangeMap rankOneDPBaseChangeInverse
    rankOneDPBaseChangeMap_comp_inverse rankOneDPBaseChangeInverse_comp_map

/-- 一般基底変更同型の全純テンソル上の具体式。 -/
theorem rankOneDPBaseChangeUniversalEquiv_tmul (b : B) (t : DividedPowerAlgebra A A) :
    rankOneDPBaseChangeUniversalEquiv (b ⊗ₜ[A] t) =
      algebraMap B (DividedPowerAlgebra B B) b *
        DividedPowerAlgebra.map B (Algebra.linearMap A B) t := rfl

/-- 一般基底変更同型の逆は全分冪生成元で指定されたテンソル族に一致する。 -/
theorem rankOneDPBaseChangeUniversalEquiv_symm_dp (n : ℕ) (b : B) :
    (rankOneDPBaseChangeUniversalEquiv (A := A) (B := B)).symm
      (DividedPowerAlgebra.dp B n b) = rankOneDPTensorValue (A := A) n b :=
  rankOneDPBaseChangeInverse_dp n b

end SerrePositivity.BhattScholze
