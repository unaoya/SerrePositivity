module
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtension
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHomValues

/-! # 元の右側延長と実 Serre tensor 分割
概要：右側自由座標の延長を、元の Serre tensor 分割の前後合成で回収する。
方針：元の右単位と結合替えの自然性を右側次元について帰納する。
規約：元の余モノイド射と因子順を保持。使われ方：標準面表示の分割合成との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右側延長は、元の Serre tensor 分割と同じ右側恒等の tensor と厳密に可換。 -/
lemma serreCubeRightExtension_tensor {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) (t : ℕ) :
    serreCubeRightExtension A f t ≫ (serreCubeTensorIso A m t).hom =
      (serreCubeTensorIso A n t).hom ≫ serreCubeTensorHom A f (𝟙 (serreCubeComonoid A t)) := by
  induction t with
  | zero =>
    change f ≫ (ρ_ (serreCubeComonoid A m)).inv =
      (ρ_ (serreCubeComonoid A n)).inv ≫ (f ⊗ₘ 𝟙 (𝟙_ (Comon (Complex A))))
    simpa only [tensorHom_id] using rightUnitor_inv_naturality f
  | succ t ih =>
    rw [serreCubeRightExtension_succ, serreCubeTensorIso_succ_hom,
      serreCubeTensorIso_succ_hom]
    change (serreCubeRightExtension A f t ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
      ((serreCubeTensorIso A m t).hom ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        (α_ (serreCubeComonoid A m) (serreCubeComonoid A t) (serreIntervalComonoid A)).hom =
      ((serreCubeTensorIso A n t).hom ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        (α_ (serreCubeComonoid A n) (serreCubeComonoid A t) (serreIntervalComonoid A)).hom ≫
          (f ⊗ₘ 𝟙 (serreCubeComonoid A t ⊗ serreIntervalComonoid A))
    have hi : serreCubeRightExtension A f t ≫ (serreCubeTensorIso A m t).hom =
        (serreCubeTensorIso A n t).hom ≫ (f ⊗ₘ 𝟙 (serreCubeComonoid A t)) := ih
    rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, hi,
      monoidalRightTensorMap_comp]
    rw [Category.assoc]
    exact congrArg (fun k => ((serreCubeTensorIso A n t).hom ⊗ₘ
      𝟙 (serreIntervalComonoid A)) ≫ k)
      (by
        simpa only [tensorHom_id, id_whiskerRight] using
          (MonoidalCategory.associator_naturality f (𝟙 (serreCubeComonoid A t))
            (𝟙 (serreIntervalComonoid A))))

/-- 元の右側延長は、元の Serre tensor 比較と同じ右側恒等の tensor の共役そのもの。 -/
lemma serreCubeRightExtension_tensor_conjugate {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) (t : ℕ) :
    serreCubeRightExtension A f t =
      (serreCubeTensorIso A n t).hom ≫ serreCubeTensorHom A f (𝟙 (serreCubeComonoid A t)) ≫
        (serreCubeTensorIso A m t).inv :=
  ((Iso.eq_comp_inv (serreCubeTensorIso A m t)).mpr
    (serreCubeRightExtension_tensor A f t)).trans (Category.assoc _ _ _)

/-- 元の右側延長の underlying 鎖射も、同じ元の tensor 比較の前後合成を回収する。 -/
lemma serreCubeRightExtension_tensor_chain {n m : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A m) (t : ℕ) :
    (serreCubeRightExtension A f t).hom =
      (serreCubeTensorIso A n t).hom.hom ≫ (f.hom ⊗ₘ 𝟙 (serreCubeComplex A t)) ≫
        (serreCubeTensorIso A m t).inv.hom := by
  have h := congrArg (fun g => g.hom) (serreCubeRightExtension_tensor_conjugate A f t)
  exact h

end SerrePositivity.KST.SConstruction
