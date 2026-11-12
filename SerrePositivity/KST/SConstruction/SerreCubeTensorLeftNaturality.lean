module
public import SerrePositivity.KST.SConstruction.SerreCubeRightKeepNaturality
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHom
public import SerrePositivity.KST.SConstruction.ConcreteCubeTensorWhisker
public import SerrePositivity.KST.SConstruction.MonoidalRightTensorStep

/-! # 元の連結 tensor 比較の左因子に関する自然性
概要：任意個の右端保持と、左因子の元の Serre 射との連結比較が厳密に可換となる。
方針：元の右端保持の評価保存と、抽象的な tensor 比較の帰納段階を合成する。
規約：全ての鎖立方体の次元を明示する。使われ方：連結積の鎖関手の tensor 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 連結比較は、左因子の元の全具体的射について自然。 -/
lemma serreCubeTensorIso_naturality_left (k : ℕ) {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube} (f : X ⟶ Y) :
    (serreConcreteCubeFunctor A).map ((concreteCubeRightWhisker k).map f) ≫
        (serreCubeTensorIso A Y.dimension k).hom =
      (serreCubeTensorIso A X.dimension k).hom ≫
        serreCubeTensorHom A (n := X.dimension) (p := Y.dimension) (m := k) (q := k)
          ((serreConcreteCubeFunctor A).map f) (𝟙 (serreCubeComonoid A k)) := by
  induction k with
  | zero =>
    exact monoidalRightTensorMap_unit (X := serreCubeComonoid A X.dimension)
      (Y := serreCubeComonoid A Y.dimension) ((serreConcreteCubeFunctor A).map f)
  | succ k ih =>
    erw [concreteCubeRightWhisker_succ_map, serreConcreteCubeRightKeep_tensor_map]
    let a : serreCubeComonoid A X.dimension ⟶ serreCubeComonoid A Y.dimension :=
      (serreConcreteCubeFunctor A).map f
    let b : serreCubeComonoid A (X.dimension + k) ⟶
        serreCubeComonoid A (Y.dimension + k) :=
      (serreConcreteCubeFunctor A).map ((concreteCubeRightWhisker k).map f)
    have hb : b ≫ (serreCubeTensorIso A Y.dimension k).hom =
        (serreCubeTensorIso A X.dimension k).hom ≫
          serreCubeTensorHom A (n := X.dimension) (p := Y.dimension) (m := k) (q := k)
            a (𝟙 (serreCubeComonoid A k)) := ih
    have ht := monoidalRightTensor_step (M := serreCubeComonoid A X.dimension)
      (N := serreCubeComonoid A Y.dimension) (R := serreCubeComonoid A (X.dimension + k))
      (S := serreCubeComonoid A (Y.dimension + k)) (U := serreCubeComonoid A k)
      (I := serreIntervalComonoid A) a b
      (serreCubeTensorIso A X.dimension k).hom (serreCubeTensorIso A Y.dimension k).hom hb
    dsimp only [serreCubeRightTensorMap, serreCubeTensorHom, serreCubeTensorIso_succ,
      Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    change (b ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
        ((serreCubeTensorIso A Y.dimension k).hom ⊗ₘ 𝟙 _) ≫
          (α_ _ _ _).hom =
      (((serreCubeTensorIso A X.dimension k).hom ⊗ₘ 𝟙 _) ≫
        (α_ _ _ _).hom) ≫ (a ⊗ₘ 𝟙 (serreCubeComonoid A k ⊗ serreIntervalComonoid A))
    rw [Category.assoc]
    exact ht

/-- 元の連結積の右恒等因子について、鎖の tensor 比較は自然。 -/
lemma serreCubeTensorIso_tensorMap_naturality_left (k : ℕ) {X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube}
    (f : X ⟶ Y) :
    (serreConcreteCubeFunctor A).map (concreteCubeTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k))) ≫
        (serreCubeTensorIso A Y.dimension k).hom =
      (serreCubeTensorIso A X.dimension k).hom ≫
        serreCubeTensorHom A (n := X.dimension) (p := Y.dimension) (m := k) (q := k)
          ((serreConcreteCubeFunctor A).map f) (𝟙 (serreCubeComonoid A k)) := by
  rw [concreteCubeTensorMap_id_right]
  exact serreCubeTensorIso_naturality_left A k f

end SerrePositivity.KST.SConstruction
