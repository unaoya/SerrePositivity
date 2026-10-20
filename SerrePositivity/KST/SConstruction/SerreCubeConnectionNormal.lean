module
public import SerrePositivity.KST.SConstruction.CubeConnectionNormalDetection
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionRelations
public import SerrePositivity.KST.SConstruction.SerreCubeConnectionFarRelations

/-! # ブロック標準表示の元の Serre 評価
概要：標準表示を元の右端 max と tensor 恒等で評価し、任意座標の隣接結合と照合する。
方針：元の max の結合則・遠座標の交換と tensor 合成則を用いる。
規約：元の Serre 余モノイド射そのものを比較する。使われ方：max の語の表示非依存性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 任意の隣接結合は、右端結合との合成で結合則または遠座標交換を満たす。 -/
lemma serreCubeConnection_slide_zero (m : ℕ) (i : Fin (m + 1)) :
    serreCubeConnection A (m + 1) i.succ ≫ serreCubeConnection A m 0 =
      serreCubeConnection A (m + 1) 0 ≫ serreCubeConnection A m i := by
  cases m with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa only [Fin.castSucc_zero] using (serreCubeConnection_assoc A 0 0).symm
  | succ m =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [Fin.castSucc_zero] using (serreCubeConnection_assoc A (m + 1) 0).symm
    · exact serreCubeConnection_connection_far_zero A m i

/-- 任意の元の prefix 射の後で、右端 max と隣接結合を交換する。 -/
lemma serreCubeConnection_tensor_slide {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A (m + 2)) (i : Fin (m + 1)) :
    ((f ≫ serreCubeConnection A m i) ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        serreCubeConnection A m 0 =
      ((f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫ serreCubeConnection A (m + 1) 0) ≫
        serreCubeConnection A m i := by
  let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 3) :=
    f ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have ht : ((f ≫ serreCubeConnection A m i) ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      g ≫ serreCubeConnection A (m + 1) i.succ := by
    change ((f ≫ serreCubeConnection A m i) ⊗ₘ 𝟙 (serreIntervalComonoid A)) =
      (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        (serreCubeConnection A m i ⊗ₘ 𝟙 (serreIntervalComonoid A))
    simp
  rw [ht]
  change (g ≫ serreCubeConnection A (m + 1) i.succ) ≫ serreCubeConnection A m 0 =
    (g ≫ serreCubeConnection A (m + 1) 0) ≫ serreCubeConnection A m i
  rw [Category.assoc, Category.assoc, serreCubeConnection_slide_zero]

/-- ブロック標準表示の元の Serre 余モノイド射による評価。 -/
def serreCubeConnectionNormal : {n m : ℕ} → CubeConnectionNormal n m →
    (serreCubeComonoid A n ⟶ serreCubeComonoid A m)
  | _, _, .nil => 𝟙 _
  | _, _, .keep d => serreCubeConnectionNormal d ⊗ₘ 𝟙 (serreIntervalComonoid A)
  | _, _, .merge d => (serreCubeConnectionNormal d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      serreCubeConnection A _ 0

/-- 一ブロックずつの標準表示は、元の Serre 恒等射。 -/
lemma serreCubeConnectionNormal_id (n : ℕ) :
    serreCubeConnectionNormal A (cubeConnectionNormalId n) = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (serreCubeConnectionNormal A (cubeConnectionNormalId n) ⊗ₘ
      𝟙 (serreIntervalComonoid A)) = 𝟙 _
    rw [ih]
    simp

/-- 標準表示の一結合は、元の同じ Serre connection との合成を厳密に回収する。 -/
lemma serreCubeConnectionNormal_connect {n m : ℕ} (d : CubeConnectionNormal n (m + 2))
    (i : Fin (m + 1)) :
    serreCubeConnectionNormal A (cubeConnectionNormalConnect d i) =
      serreCubeConnectionNormal A d ≫ serreCubeConnection A m i := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | keep d =>
      cases m with
      | zero =>
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        rfl
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · rfl
        · change (serreCubeConnectionNormal A (cubeConnectionNormalConnect d i) ⊗ₘ
              𝟙 (serreIntervalComonoid A)) =
            (serreCubeConnectionNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeConnection A m i ⊗ₘ 𝟙 (serreIntervalComonoid A))
          rw [ih d i]
          simp only [tensorHom_comp_tensorHom, Category.comp_id]
    | merge d =>
      rw [cubeConnectionNormalConnect]
      change (serreCubeConnectionNormal A (cubeConnectionNormalConnect d i) ⊗ₘ
          𝟙 (serreIntervalComonoid A)) ≫ serreCubeConnection A m 0 =
        ((serreCubeConnectionNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          serreCubeConnection A (m + 1) 0) ≫ serreCubeConnection A m i
      rw [ih d i]
      exact serreCubeConnection_tensor_slide A (serreCubeConnectionNormal A d) i

end SerrePositivity.KST.SConstruction
