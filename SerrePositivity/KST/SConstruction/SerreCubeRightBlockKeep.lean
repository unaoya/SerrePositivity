module
public import SerrePositivity.KST.SConstruction.ConcreteCubeRightBlockHom
public import SerrePositivity.KST.SConstruction.SerreCubeRightKeepNaturality
public import SerrePositivity.KST.SConstruction.SerreConcreteCubeMap
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHomValues
public import SerrePositivity.KST.SConstruction.MonoidalRightBlockNaturality

/-! # 元の右ブロック保持の評価と鎖比較の帰納段階
概要：具体的射の評価の式と、任意の固定した鎖射の tensor 帰納段階を分けて証明する。
方針：元の右端保持の回収と抽象的 tensor の法則を、それぞれ固定した型で検証する。
規約：全次元と元の比較射を保つ。使われ方：全具体的射の右因子自然性の保持工程。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右ブロック保持の評価は、元の連結射の右 tensor。 -/
lemma serreCubeRightBlock_keep_evaluation (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) :
    serreConcreteCubeMap A
        (concreteCubeRightBlockHom n (concreteCubeRightKeepHom f)) =
      serreCubeRightTensorMap A (n := n + m) (m := n + k)
        (serreConcreteCubeMap A (concreteCubeRightBlockHom n f)) :=
  (congrArg (fun t => serreConcreteCubeMap A t)
    (concreteCubeRightBlockHom_keep n f)).trans
    (serreConcreteCubeRightKeep_tensor A (concreteCubeRightBlockHom n f))

/-- 次元を固定した元の Serre 射は、元の右端保持を回収する。 -/
lemma serreConcreteCubeMap_keep {n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk n ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m) :
    serreConcreteCubeMap A (concreteCubeRightKeepHom f) =
      serreCubeRightTensorMap A (n := n) (m := m) (serreConcreteCubeMap A f) :=
  serreConcreteCubeRightKeep_tensor A f

/-- 固定した元の鎖射の可換四角形を、右端保持の同じ連結比較へ移す。 -/
lemma serreCubeTensor_rightKeep_step (n m k : ℕ)
    (b : serreCubeComonoid A (n + m) ⟶ serreCubeComonoid A (n + k))
    (a : serreCubeComonoid A m ⟶ serreCubeComonoid A k)
    (h : b ≫ (serreCubeTensorIso A n k).hom =
      (serreCubeTensorIso A n m).hom ≫
        serreCubeTensorHom A (n := n) (p := n) (m := m) (q := k)
          (𝟙 (serreCubeComonoid A n)) a) :
    serreCubeRightTensorMap A (n := n + m) (m := n + k) b ≫
        (serreCubeTensorIso A n (k + 1)).hom =
      (serreCubeTensorIso A n (m + 1)).hom ≫
        serreCubeTensorHom A (n := n) (p := n) (m := m + 1) (q := k + 1)
          (𝟙 (serreCubeComonoid A n)) (serreCubeRightTensorMap A (n := m) (m := k) a) := by
  have ht := monoidalRightBlock_keep_comparison (R := serreCubeComonoid A (n + m))
    (S := serreCubeComonoid A (n + k)) (X := serreCubeComonoid A n)
    (Y := serreCubeComonoid A m) (Z := serreCubeComonoid A k) (I := serreIntervalComonoid A)
    (serreCubeTensorIso A n m).hom (serreCubeTensorIso A n k).hom b a h
  erw [serreCubeTensorIso_succ_hom A n k, serreCubeTensorIso_succ_hom A n m]
  dsimp only [serreCubeTensorHom, serreCubeRightTensorMap]
  apply Comon.ext
  exact congrArg (fun f => f.hom) ht

end SerrePositivity.KST.SConstruction
