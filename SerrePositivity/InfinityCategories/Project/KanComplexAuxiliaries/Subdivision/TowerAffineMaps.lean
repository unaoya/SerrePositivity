module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TowerLimOne
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：群の塔と twisted 方程式のアフィンな塔。
方針：群の遷移を右平行移動し、任意の合成も右平行移動であることを帰納的に示す。
規約：可換性は不要。右側の平行移動を使うので因子の順序を保つ。
使われ方：Goerss–Jardine VIII §1。Mittag–Leffler 条件の twisted 逆系への移送。
-/

@[expose] public section
universe u
open CategoryTheory Opposite

namespace SerrePositivity.KST.Spectra.TowerLimOne
end SerrePositivity.KST.Spectra.TowerLimOne
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.TowerLimOne

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : ℕ → Type u) [∀ n, Group (G n)] (q : ∀ n, G (n + 1) →* G n)

/-- 群の遷移列から作る逐次逆系。 -/
abbrev groupTower : ℕᵒᵖ ⥤ GrpCat.{u} :=
  Functor.ofOpSequence (X := fun n ↦ GrpCat.of (G n)) (fun n ↦ GrpCat.ofHom (q n))

/-- 群の塔の遷移を元の型上の準同型として取り出す。 -/
def transition {i j : ℕᵒᵖ} (f : i ⟶ j) : G i.unop →* G j.unop :=
  ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.groupTower G q).map f).hom

/-- 群の遷移の合成の値。 -/
lemma transition_comp {i j k : ℕᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) (a : G i.unop) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q (f ≫ g) a = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q g (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q f a) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition]
  rw [Functor.map_comp]
  rfl

/-- twisted 方程式を整合条件とする右アフィンな逐次逆系。 -/
abbrev affineTower (x : ∀ n, G n) : ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (X := G) (fun n ↦ ↾(fun a ↦ q n a * (x n)⁻¹))

/-- 群の塔の隣接射は指定した準同型。 -/
lemma groupTower_step (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.groupTower G q).map (homOfLE (Nat.le_succ n)).op = GrpCat.ofHom (q n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-- アフィンな塔の隣接射は twisted 方程式の右平行移動。 -/
lemma affineTower_step (x : ∀ n, G n) (n : ℕ) (a : G (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map (homOfLE (Nat.le_succ n)).op a = q n a * (x n)⁻¹ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- 合成したアフィンな遷移も元の合成した準同型の右平行移動。 -/
lemma affineTower_map (x : ∀ n, G n) (i j : ℕ) (hij : i ≤ j) :
    ∃ c : G i, ∀ a : G j,
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map (homOfLE hij).op a =
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q (homOfLE hij).op a * c := by
  induction j, hij using Nat.le_induction with
  | base =>
    refine ⟨1, fun a ↦ ?_⟩
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition]
    rfl
  | succ j hij ih =>
    obtain ⟨c, hc⟩ := ih
    let h : op j ⟶ op i := (homOfLE hij).op
    let g : op (j + 1) ⟶ op j := (homOfLE (Nat.le_succ j)).op
    have he : (homOfLE (hij.trans (Nat.le_succ j))).op = g ≫ h := Subsingleton.elim _ _
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q h) ((x j)⁻¹) * c, fun a ↦ ?_⟩
    rw [he, Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition_comp]
    change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map h ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower G q x).map g a) =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q h) ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q g) a) *
        ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q h) ((x j)⁻¹) * c)
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.affineTower_step, hc, map_mul, ← mul_assoc]
    have hg (a : G (j + 1)) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition G q g a = q j a := by
      dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.transition]
      rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.groupTower_step]
      rfl
    rw [hg]

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
