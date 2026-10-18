module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeMap

/-!
概要：KST Def3.1 の Koszul 生成元を一つ追加する際の総外積の分解。
方針：M×R の最後の座標で収縮し、最後の生成元を含む部分と含まない部分を回収する。
規約：最後の生成元は左から外積する。反復 cone の符号比較は別工程。
使われ方：外積 Koszul 模型と反復 cone 模型の比較の帰納段階。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：M の外積を M×R の外積に埋め込む。
方針：第一因子の線形包含を外積に延長する。
規約：KST Def3.1。使われ方：最後の生成元を含まない部分。 -/
abbrev exteriorProductIn : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R (M × R) :=
  ExteriorAlgebra.map (LinearMap.inl R M R)

/-- 概要：M×R の外積から最後の生成元を消す。
方針：第一因子への射影を外積に延長する。
規約：KST Def3.1。使われ方：二成分分解の第一成分。 -/
abbrev exteriorProductOut : ExteriorAlgebra R (M × R) →ₐ[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.map (LinearMap.fst R M R)

/-- 概要：追加した最後の生成元。
方針：M×R の (0,1) を次数1に埋め込む。
規約：KST Def3.1。使われ方：二成分分解の第二成分の復元。 -/
abbrev exteriorProductLast : ExteriorAlgebra R (M × R) :=
  ExteriorAlgebra.ι R (0, (1 : R))

/-- 概要：射影後に包含した外積は元に戻る。
方針：線形写像 fst∘inl=id の外積への関手性。
規約：KST Def3.1。使われ方：外積二成分分解の逆元律。 -/
@[simp] theorem exteriorProductOut_in (z : ExteriorAlgebra R M) :
    exteriorProductOut (exteriorProductIn z) = z := by
  change ExteriorAlgebra.map (LinearMap.fst R M R)
    (ExteriorAlgebra.map (LinearMap.inl R M R) z) = z
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  have h : (LinearMap.fst R M R).comp (LinearMap.inl R M R) = LinearMap.id := by ext; rfl
  rw [h]
  exact AlgHom.congr_fun ExteriorAlgebra.map_id z

/-- 概要：最後の座標での収縮は第一因子の外積上で零。
方針：収縮の自然性と snd∘inl=0 を使う。
規約：KST Def3.1。使われ方：二成分分解の逆元律。 -/
@[simp] theorem exteriorProduct_contract_in (z : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := 0) (LinearMap.snd R M R)
      (exteriorProductIn z) = 0 := by
  have h : (LinearMap.snd R M R).comp (LinearMap.inl R M R) = 0 := by ext; rfl
  rw [exteriorContraction_map (LinearMap.inl R M R) 0 (LinearMap.snd R M R) h]
  simp

/-- 概要：総外積を最後の生成元を含まない部分と含む部分へ分解する。
方針：係数・和・生成元による左乗法で帰納し、最後の生成元の平方零と反可換性を使う。
規約：KST Def3.1、最後の生成元は左に置く。使われ方：cone 比較の次数別直和分解。 -/
theorem exteriorProduct_decomposition (z : ExteriorAlgebra R (M × R)) :
    z = exteriorProductIn (exteriorProductOut z) +
      exteriorProductLast * exteriorProductIn (exteriorProductOut
        (CliffordAlgebra.contractLeft (Q := 0) (LinearMap.snd R M R) z)) := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add z w hz hw =>
    simp only [map_add, mul_add]
    rw [add_add_add_comm]
    exact congrArg₂ (· + ·) hz hw
  | ι_mul z m hz =>
    have hm : ExteriorAlgebra.ι R m =
        ExteriorAlgebra.ι R (m.1, (0 : R)) + m.2 • exteriorProductLast (M := M) := by
      rw [← map_smul, ← map_add]
      congr 1
      ext <;> simp
    have ha : ExteriorAlgebra.ι R (m.1, (0 : R)) * exteriorProductLast =
        -(exteriorProductLast * ExteriorAlgebra.ι R (m.1, (0 : R))) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (m.1, (0 : R)) (0, 1))
    have he : exteriorProductLast (R := R) (M := M) * exteriorProductLast = 0 :=
      ExteriorAlgebra.ι_sq_zero _
    simp only [CliffordAlgebra.contractLeft_ι_mul, map_mul, map_sub, map_smul,
      ExteriorAlgebra.map_apply_ι, LinearMap.fst_apply, LinearMap.snd_apply,
      LinearMap.inl_apply]
    calc
      ExteriorAlgebra.ι R m * z =
          (ExteriorAlgebra.ι R (m.1, (0 : R)) + m.2 • exteriorProductLast) *
            (exteriorProductIn (exteriorProductOut z) +
              exteriorProductLast * exteriorProductIn (exteriorProductOut
                (CliffordAlgebra.contractLeft (Q := 0) (LinearMap.snd R M R) z))) := by
        rw [← hm, ← hz]
      _ = _ := by
        simp only [add_mul, mul_add, smul_mul_assoc, ← mul_assoc, ha, he,
          smul_zero, add_zero, neg_mul, mul_sub, mul_smul_comm]
        abel

end SerrePositivity.KST.DerivedBlowup
