module
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateLaws
public import SerrePositivity.KST.SConstruction.ComonoidStructureMaps

/-! # 座標余モノイド射の元の鎖写像の回収
概要：全座標の面・退化・connection は、元の tensor 鎖写像の再帰式を回収する。
方針：余モノイドの構造射と tensor の基礎の射を忘却する。
規約：別の chain map を選ばない。使われ方：cubical rigidification の生成元での照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 右端への面は、元の右単位射と同じ端点 chain map の tensor。 -/
lemma serreCubeFace_zero_hom (b : Bool) (n : ℕ) :
    (serreCubeFace A b n 0).hom = (ρ_ (serreCubeComplex A n)).inv ≫
      (𝟙 (serreCubeComplex A n) ⊗ₘ (serreIntervalEndpointComonHom A b).hom) := by
  simp only [serreCubeFace_zero, Comon.comp_hom', Comon.id_hom',
    Comon.monoidal_tensorHom_hom, comonoidRightUnitorInvHom]


/-- 内側の面の基礎の chain map は、同じ一段小さい面の tensor。 -/
lemma serreCubeFace_succ_hom (b : Bool) (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeFace A b (n + 1) i.succ).hom =
      (serreCubeFace A b n i).hom ⊗ₘ 𝟙 (serreInterval A) := by
  rw [serreCubeFace_succ]
  rfl

/-- 右端の退化は、元の増大 chain map と右単位射。 -/
lemma serreCubeDegeneracy_zero_hom (n : ℕ) :
    (serreCubeDegeneracy A n 0).hom =
      (𝟙 (serreCubeComplex A n) ⊗ₘ serreIntervalAugmentation A) ≫
        (ρ_ (serreCubeComplex A n)).hom := by
  simp only [serreCubeDegeneracy_zero, Comon.comp_hom', Comon.id_hom',
    Comon.monoidal_tensorHom_hom, comonoidRightUnitorHom,
    serreIntervalAugmentationComonHom_hom]


/-- 内側の退化の基礎の chain map は、同じ一段小さい退化の tensor。 -/
lemma serreCubeDegeneracy_succ_hom (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeDegeneracy A (n + 1) i.succ).hom =
      (serreCubeDegeneracy A n i).hom ⊗ₘ 𝟙 (serreInterval A) := by
  rw [serreCubeDegeneracy_succ]
  rfl

/-- 右端の connection は、元の結合 chain map と max の tensor。 -/
lemma serreCubeConnection_zero_hom (n : ℕ) :
    (serreCubeConnection A n 0).hom =
      (α_ (serreCubeComplex A n) (serreInterval A) (serreInterval A)).hom ≫
        (𝟙 (serreCubeComplex A n) ⊗ₘ serreIntervalMax A) := by
  simp only [serreCubeConnection_zero, Comon.comp_hom', Comon.id_hom',
    Comon.monoidal_tensorHom_hom, comonoidAssociatorHom,
    serreIntervalMaxComonHom_hom]
  rfl

/-- 内側の connection の基礎の chain map は、同じ一段小さい connection の tensor。 -/
lemma serreCubeConnection_succ_hom (n : ℕ) (i : Fin (n + 1)) :
    (serreCubeConnection A (n + 1) i.succ).hom =
      (serreCubeConnection A n i).hom ⊗ₘ 𝟙 (serreInterval A) := by
  rw [serreCubeConnection_succ]
  rfl

end SerrePositivity.KST.SConstruction
