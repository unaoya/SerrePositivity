module
public import SerrePositivity.KST.SConstruction.SerreCubeFaceConnectionResult

/-! # 面の後の connection の正規化の元の Serre 評価保存
概要：定数の単位・吸収、入力同士の結合を元の射で照合し、全座標へ拡張する。
方針：prefix 補題、右端 connection の自然性、遠座標の面交換を適用する。
規約：元の余モノイド射の等号。使われ方：一般の混合語の三段正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 面の後の右端 connection の正規化は、元の Serre 評価を厳密に保存する。 -/
lemma serreCubeFaceNormal_connectZero {n m : ℕ} (d : CubeFaceNormal n (m + 2)) :
    serreCubeFaceConnectionResult A (cubeFaceNormalConnectZero d) =
      serreCubeFaceNormal A d ≫ serreCubeConnection A m 0 := by
  cases d with
  | point b d =>
    cases b with
    | false =>
      change serreCubeFaceNormal A d =
        (serreCubeFaceNormal A d ≫ serreCubeFace A false (m + 1) 0) ≫
          serreCubeConnection A m 0
      rw [Category.assoc, serreCubeFace_zero_connection_right, Category.comp_id]
    | true =>
      cases d with
      | point c d =>
        change serreCubeFaceNormal A d ≫ serreCubeFace A true m 0 =
          ((serreCubeFaceNormal A d ≫ serreCubeFace A c m 0) ≫
            serreCubeFace A true (m + 1) 0) ≫ serreCubeConnection A m 0
        have h := congrArg (fun f => serreCubeFaceNormal A d ≫ f)
          (serreCubeFace_connection_constants A true c m)
        simpa only [Category.assoc, Bool.max_eq_or, Bool.true_or] using h.symm
      | keep d =>
        exact (serreCubeFace_connection_right_one_prefix A (serreCubeFaceNormal A d)).symm
  | keep d =>
    cases d with
    | point b d =>
      cases b with
      | false =>
        exact (serreCubeFace_connection_left_zero_prefix A (serreCubeFaceNormal A d)).symm
      | true =>
        exact (serreCubeFace_connection_left_one_prefix A (serreCubeFaceNormal A d)).symm
    | keep d =>
      exact (serreCubeConnection_zero_naturality A (serreCubeFaceNormal A d)).symm

/-- 面の後の任意座標の connection の正規化は、元の Serre 評価を厳密に保存する。 -/
lemma serreCubeFaceNormal_connect {n m : ℕ} (d : CubeFaceNormal n (m + 2))
    (i : Fin (m + 1)) :
    serreCubeFaceConnectionResult A (cubeFaceNormalConnect d i) =
      serreCubeFaceNormal A d ≫ serreCubeConnection A m i := by
  induction m generalizing n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    exact serreCubeFaceNormal_connectZero A d
  | succ m ih =>
    cases d with
    | point b d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · exact serreCubeFaceNormal_connectZero A _
      · change serreCubeFaceConnectionResult A
          (cubeFaceConnectionResultPoint b (cubeFaceNormalConnect d i)) = _
        rw [serreCubeFaceConnectionResult_point, ih d i]
        change (serreCubeFaceNormal A d ≫ serreCubeConnection A m i) ≫
          serreCubeFace A b (m + 1) 0 =
            (serreCubeFaceNormal A d ≫ serreCubeFace A b (m + 2) 0) ≫
              serreCubeConnection A (m + 1) i.succ
        simp only [Category.assoc]
        rw [serreCubeFace_connection_right_far_zero]
    | keep d =>
      refine Fin.cases ?_ (fun i => ?_) i
      · exact serreCubeFaceNormal_connectZero A _
      · change serreCubeFaceConnectionResult A
          (cubeFaceConnectionResultKeep (cubeFaceNormalConnect d i)) = _
        rw [serreCubeFaceConnectionResult_keep]
        change (serreCubeFaceConnectionResult A (cubeFaceNormalConnect d i) ⊗ₘ
            𝟙 (serreIntervalComonoid A)) =
          (serreCubeFaceNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
            (serreCubeConnection A m i ⊗ₘ 𝟙 (serreIntervalComonoid A))
        rw [ih d i]
        simp only [tensorHom_comp_tensorHom, Category.comp_id]

end SerrePositivity.KST.SConstruction
