module
public import SerrePositivity.KST.SConstruction.ConcreteCubeRightBlockHom
public import SerrePositivity.KST.SConstruction.SerreCubeRightBlockZero
public import SerrePositivity.KST.SConstruction.SerreCubeRightBlockKeep
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHomLaws

/-! # 元の右ブロックの鎖比較の可換条件
概要：右ブロックの元の具体的射に対する連結比較の自然性条件と右端保持の保存を定義する。
方針：元の入力・出力と鎖射を固定し、右 tensor の評価と抽象的帰納段階を使う。
規約：追加の入力仮定を定義に置かない。使われ方：全座標と全生成語の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右ブロック射に関する、元の連結比較の可換性そのもの。 -/
def SerreCubeRightBlockNatural (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) : Prop :=
  serreConcreteCubeMap A (concreteCubeRightBlockHom n f) ≫
      (serreCubeTensorIso A n k).hom =
    (serreCubeTensorIso A n m).hom ≫
      serreCubeTensorHom A (n := n) (p := n) (m := m) (q := k)
        (𝟙 (serreCubeComonoid A n)) (serreConcreteCubeMap A f)

/-- 元の二つの射の評価を固定した可換四角形から、元の右ブロック自然性を回収する。 -/
lemma serreCubeRightBlockNatural_of_evaluations (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k)
    (b : serreCubeComonoid A (n + m) ⟶ serreCubeComonoid A (n + k))
    (a : serreCubeComonoid A m ⟶ serreCubeComonoid A k)
    (hb : serreConcreteCubeMap A (concreteCubeRightBlockHom n f) = b)
    (ha : serreConcreteCubeMap A f = a)
    (h : b ≫ (serreCubeTensorIso A n k).hom = (serreCubeTensorIso A n m).hom ≫
      serreCubeTensorHom A (n := n) (p := n) (m := m) (q := k)
        (𝟙 (serreCubeComonoid A n)) a) : SerreCubeRightBlockNatural A n f := by
  dsimp only [SerreCubeRightBlockNatural]
  rw [hb, ha]
  exact h

/-- 右ブロックの自然性は、元の右端保持で保存される。 -/
lemma serreCubeRightBlockNatural_keep (n : ℕ) {m k : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk m ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk k) (hf : SerreCubeRightBlockNatural A n f) :
    SerreCubeRightBlockNatural A n (concreteCubeRightKeepHom f) := by
  dsimp only [SerreCubeRightBlockNatural] at hf ⊢
  erw [serreCubeRightBlock_keep_evaluation A n f, serreConcreteCubeMap_keep A f]
  exact serreCubeTensor_rightKeep_step A n m k
    (serreConcreteCubeMap A (concreteCubeRightBlockHom n f))
    (serreConcreteCubeMap A f) hf

end SerrePositivity.KST.SConstruction
