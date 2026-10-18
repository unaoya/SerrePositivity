module

public import SerrePositivity.KST.DerivedBlowup.ChartExterior

/-!
概要：KST Lemma3.6 の例外因子の Koszul 関係式を全 a_j の列へ変換する。
方針：pivot の基底は固定し、他の e_j を S_j e_i−e_j へ送る反転写像を作る。
規約：全添字を持つ自由加群に戻す。外積と反復 cone の比較は別定理。
使われ方：E∩U_i の Ko(A;a)[S] への同定に必要な可逆基底変換。
-/

@[expose] public noncomputable section

universe v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I] {B : Type w} [CommRing B]

/-- 概要：例外因子の全関係式への可逆基底変換の線形写像。
方針：pivot を固定し、他を x_j e_i−e_j に送る。
規約：KST Lemma3.6。使われ方：Cartier 方程式を加えた Koszul の変換。 -/
def exceptionalGeneratorMap (i : I) (x : I → B) : (I →₀ B) →ₗ[B] (I →₀ B) :=
  Finsupp.linearCombination B (fun j =>
    if j = i then Finsupp.single i 1 else x j • Finsupp.single i 1 - Finsupp.single j 1)

/-- 概要：例外因子の基底変換の生成元公式。
方針：自由加群の普遍性で計算する。規約：KST Lemma3.6。
使われ方：反転性と関係式への適合性。 -/
theorem exceptionalGeneratorMap_single (i j : I) (x : I → B) :
    exceptionalGeneratorMap i x (Finsupp.single j 1) =
      if j = i then Finsupp.single i 1 else
        x j • Finsupp.single i 1 - Finsupp.single j 1 := by
  simp [exceptionalGeneratorMap]

/-- 概要：例外因子の基底変換を二回施すと生成元を回収する。
方針：pivot 固定と他の生成元の二項変換を計算する。
規約：KST Lemma3.6、正則性は不要。使われ方：変換の可逆性。 -/
theorem exceptionalGeneratorMap_involutive_single (i j : I) (x : I → B) :
    exceptionalGeneratorMap i x (exceptionalGeneratorMap i x (Finsupp.single j 1)) =
      Finsupp.single j 1 := by
  by_cases h : j = i
  · subst j
    simp [exceptionalGeneratorMap_single]
  · rw [exceptionalGeneratorMap_single, ite_eq_right h, map_sub, map_smul,
      exceptionalGeneratorMap_single, ite_eq_left rfl,
      exceptionalGeneratorMap_single, ite_eq_right h]
    abel

/-- 概要：例外因子の基底変換は自己逆。
方針：生成元上の反転性を線形に延長する。規約：KST Lemma3.6。
使われ方：例外因子の二つの Koszul 表示の同型。 -/
theorem exceptionalGeneratorMap_comp (i : I) (x : I → B) :
    (exceptionalGeneratorMap i x).comp (exceptionalGeneratorMap i x) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j c
  have he : Finsupp.single j c = c • Finsupp.single j (1 : B) := by simp
  change exceptionalGeneratorMap i x (exceptionalGeneratorMap i x (Finsupp.single j c)) = _
  rw [he, map_smul, map_smul]
  change c • exceptionalGeneratorMap i x (exceptionalGeneratorMap i x (Finsupp.single j 1)) =
    c • Finsupp.single j 1
  rw [exceptionalGeneratorMap_involutive_single]

/-- 概要：例外因子の全関係式の生成加群間の線形同型。
方針：同じ変換を両側逆にする。規約：KST Lemma3.6。
使われ方：外積代数の同型へ持ち上げる。 -/
def exceptionalGeneratorEquiv (i : I) (x : I → B) : (I →₀ B) ≃ₗ[B] (I →₀ B) :=
  LinearEquiv.ofLinearMap (exceptionalGeneratorMap i x) (exceptionalGeneratorMap i x)
    (exceptionalGeneratorMap_comp i x) (exceptionalGeneratorMap_comp i x)

/-- 概要：pivot に Cartier 方程式、その他にチャート方程式を置く列。
方針：全添字に復元し pivot のみ a_i とする。
規約：KST Lemma3.6、全 a_j の Koszul 列との比較。使われ方：微分の係数。 -/
def exceptionalRelationValue (a x : I → B) (i j : I) : B :=
  if j = i then a i else a i * x j - a j

/-- 概要：基底変換は例外因子の関係式列を全 a_j の列へ移す。
方針：生成元上で微分を計算し係数の可換性を使う。
規約：KST Lemma3.6。使われ方：Ko(A;a)[S] との微分を保つ比較。 -/
theorem exceptionalGeneratorMap_differential (a x : I → B) (i : I) :
    (Finsupp.linearCombination B a).comp (exceptionalGeneratorMap i x) =
      Finsupp.linearCombination B (exceptionalRelationValue a x i) := by
  apply Finsupp.lhom_ext
  intro j c
  simp only [LinearMap.comp_apply, exceptionalGeneratorMap, Finsupp.linearCombination_single]
  by_cases h : j = i
  · subst j
    simp [exceptionalRelationValue]
  · simp [h, exceptionalRelationValue, map_sub, map_smul, mul_comm]

/-- 概要：例外因子の関係式の変換を外積代数の同型へ延長する。
方針：自己逆の線形変換に外積の関手性を適用する。
規約：KST Lemma3.6、微分の係数の適合は直前の定理。
使われ方：例外因子の Koszul cdga の表示比較。 -/
def exceptionalExteriorEquiv (i : I) (x : I → B) :
    ExteriorAlgebra B (I →₀ B) ≃ₐ[B] ExteriorAlgebra B (I →₀ B) :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map (exceptionalGeneratorMap i x))
    (ExteriorAlgebra.map (exceptionalGeneratorMap i x))
    (by rw [ExteriorAlgebra.map_comp_map, exceptionalGeneratorMap_comp, ExteriorAlgebra.map_id])
    (by rw [ExteriorAlgebra.map_comp_map, exceptionalGeneratorMap_comp, ExteriorAlgebra.map_id])

/-- 概要：例外因子の外積代数同型は収縮微分を保つ。
方針：生成元上の微分比較を左生成元による帰納法で全外積に延長する。
規約：KST Lemma3.6、整数次数の複体への装備は別途。
使われ方：Ko(A;a)[S] と例外因子チャートの微分代数としての比較。 -/
theorem exceptionalExteriorEquiv_differential (a x : I → B) (i : I)
    (z : ExteriorAlgebra B (I →₀ B)) :
    CliffordAlgebra.contractLeft (Q := 0) (Finsupp.linearCombination B a)
        (exceptionalExteriorEquiv i x z) =
      exceptionalExteriorEquiv i x
        (CliffordAlgebra.contractLeft (Q := 0)
          (Finsupp.linearCombination B (exceptionalRelationValue a x i)) z) := by
  change CliffordAlgebra.contractLeft (Q := 0) (Finsupp.linearCombination B a)
      (ExteriorAlgebra.map (exceptionalGeneratorMap i x) z) =
    ExteriorAlgebra.map (exceptionalGeneratorMap i x)
      (CliffordAlgebra.contractLeft (Q := 0)
        (Finsupp.linearCombination B (exceptionalRelationValue a x i)) z)
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | ι_mul z m hz =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι, hz]
    have hm := LinearMap.congr_fun (exceptionalGeneratorMap_differential a x i) m
    exact congrArg (fun c => c • ExteriorAlgebra.map (exceptionalGeneratorMap i x) z -
      ExteriorAlgebra.ι B (exceptionalGeneratorMap i x m) *
        ExteriorAlgebra.map (exceptionalGeneratorMap i x)
          (CliffordAlgebra.contractLeft (Q := 0)
            (Finsupp.linearCombination B (exceptionalRelationValue a x i)) z)) hm

end SerrePositivity.KST.DerivedBlowup
