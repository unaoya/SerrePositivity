module
public import SerrePositivity.KST.SConstruction.SerreCubeDeletionConnectionNormal

/-! # ブロック出力削除の入力側への移動と元の Serre 評価
概要：一ブロックの削除で、その全入力の削除と残余 max の評価を厳密に回収する。
方針：任意の prefix 射での右端削除と遠座標削除を先に照合し、入力次元で帰納する。
規約：検証上限を変えず、元の余モノイド射の等号を示す。使われ方：混合語の正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の任意の prefix の後の右端 max の削除は、両入力の削除を回収する。 -/
lemma serreCubeConnection_delete_zero_prefix {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A (m + 1)) :
    ((f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫ serreCubeConnection A m 0) ≫
        serreCubeDegeneracy A m 0 =
      serreCubeDegeneracy A n 0 ≫ (f ≫ serreCubeDegeneracy A m 0) := by
  let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 2) :=
    f ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have hn : g ≫ serreCubeDegeneracy A (m + 1) 0 = serreCubeDegeneracy A n 0 ≫ f :=
    serreCubeDegeneracy_zero_naturality A f
  change (g ≫ serreCubeConnection A m 0) ≫ serreCubeDegeneracy A m 0 = _
  rw [Category.assoc, serreCubeConnection_degeneracy_zero, ← Category.assoc, hn, Category.assoc]

/-- 元の任意の prefix の後の右端 max と遠い削除の交換は、同じ入力削除を回収する。 -/
lemma serreCubeConnection_delete_succ_prefix {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A (m + 2)) (i : Fin (m + 1)) :
    ((f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫ serreCubeConnection A (m + 1) 0) ≫
        serreCubeDegeneracy A (m + 1) i.succ =
      ((f ≫ serreCubeDegeneracy A (m + 1) i.succ) ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        serreCubeConnection A m 0 := by
  let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (m + 3) :=
    f ⊗ₘ 𝟙 (serreIntervalComonoid A)
  have ht : g ≫ serreCubeDegeneracy A (m + 2) i.succ.succ =
      (f ≫ serreCubeDegeneracy A (m + 1) i.succ) ⊗ₘ 𝟙 (serreIntervalComonoid A) := by
    change (f ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      (serreCubeDegeneracy A (m + 1) i.succ ⊗ₘ 𝟙 (serreIntervalComonoid A)) = _
    simp only [tensorHom_comp_tensorHom, Category.comp_id]
  change (g ≫ serreCubeConnection A (m + 1) 0) ≫
    serreCubeDegeneracy A (m + 1) i.succ = _
  rw [Category.assoc, serreCubeConnection_degeneracy_left_far_zero, ← Category.assoc, ht]
  rfl

/-- 元のブロックの一出力削除の正規化は、元の Serre 評価そのものを保存する。 -/
lemma serreCubeConnectionNormal_delete {n m : ℕ} (d : CubeConnectionNormal n (m + 1))
    (i : Fin (m + 1)) :
    serreCubeDeletionConnectionNormal A (cubeConnectionNormalDelete d i) =
      serreCubeConnectionNormal A d ≫ serreCubeDegeneracy A m i := by
  induction n generalizing m with
  | zero => cases d
  | succ n ih =>
    cases d with
    | keep d =>
      cases m with
      | zero =>
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        rw [cubeConnectionNormalDelete, serreCubeDeletionConnectionNormal_drop,
          serreCubeDeletionConnectionNormal_from]
        exact (serreCubeDegeneracy_zero_naturality A (serreCubeConnectionNormal A d)).symm
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · change serreCubeDeletionConnectionNormal A
            (cubeDeletionConnectionNormalDrop (cubeDeletionConnectionNormalFrom d)) = _
          rw [serreCubeDeletionConnectionNormal_drop, serreCubeDeletionConnectionNormal_from]
          exact (serreCubeDegeneracy_zero_naturality A (serreCubeConnectionNormal A d)).symm
        · change serreCubeDeletionConnectionNormal A
            (cubeDeletionConnectionNormalKeep (cubeConnectionNormalDelete d i)) = _
          rw [serreCubeDeletionConnectionNormal_keep, ih d i]
          change ((serreCubeConnectionNormal A d ≫ serreCubeDegeneracy A m i) ⊗ₘ
              𝟙 (serreIntervalComonoid A)) =
            (serreCubeConnectionNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
              (serreCubeDegeneracy A m i ⊗ₘ 𝟙 (serreIntervalComonoid A))
          simp only [tensorHom_comp_tensorHom, Category.comp_id]
    | merge d =>
      cases m with
      | zero =>
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        rw [cubeConnectionNormalDelete, serreCubeDeletionConnectionNormal_drop, ih d 0]
        exact (serreCubeConnection_delete_zero_prefix A (serreCubeConnectionNormal A d)).symm
      | succ m =>
        refine Fin.cases ?_ (fun i => ?_) i
        · change serreCubeDeletionConnectionNormal A
            (cubeDeletionConnectionNormalDrop (cubeConnectionNormalDelete d 0)) = _
          rw [serreCubeDeletionConnectionNormal_drop, ih d 0]
          exact (serreCubeConnection_delete_zero_prefix A (serreCubeConnectionNormal A d)).symm
        · change serreCubeDeletionConnectionNormal A
            (cubeDeletionConnectionNormalMerge (cubeConnectionNormalDelete d i.succ)) = _
          rw [serreCubeDeletionConnectionNormal_merge, ih d i.succ]
          exact (serreCubeConnection_delete_succ_prefix A (serreCubeConnectionNormal A d) i).symm

end SerrePositivity.KST.SConstruction
