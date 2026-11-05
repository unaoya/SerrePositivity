module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.TowerLimOne
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
namespace SerrePositivity.InfinityCategories.Kan.TowerLimOne
open SerrePositivity.KST.Spectra.TowerLimOne

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G : ℕ → Type u) [∀ n, Group (G n)] (q : ∀ n, G (n + 1) →* G n)

/-- 群の遷移列から作る逐次逆系。 -/
abbrev groupTower : ℕᵒᵖ ⥤ GrpCat.{u} :=
  Functor.ofOpSequence (X := fun n ↦ GrpCat.of (G n)) (fun n ↦ GrpCat.ofHom (q n))

/-- 群の塔の遷移を元の型上の準同型として取り出す。 -/
def transition {i j : ℕᵒᵖ} (f : i ⟶ j) : G i.unop →* G j.unop :=
  ((groupTower G q).map f).hom

/-- 群の遷移の合成の値。 -/
lemma transition_comp {i j k : ℕᵒᵖ} (f : i ⟶ j) (g : j ⟶ k) (a : G i.unop) :
    transition G q (f ≫ g) a = transition G q g (transition G q f a) := by
  dsimp only [transition]
  rw [Functor.map_comp]
  rfl

/-- twisted 方程式を整合条件とする右アフィンな逐次逆系。 -/
abbrev affineTower (x : ∀ n, G n) : ℕᵒᵖ ⥤ Type u :=
  Functor.ofOpSequence (X := G) (fun n ↦ ↾(fun a ↦ q n a * (x n)⁻¹))

/-- 群の塔の隣接射は指定した準同型。 -/
lemma groupTower_step (n : ℕ) :
    (groupTower G q).map (homOfLE (Nat.le_succ n)).op = GrpCat.ofHom (q n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-- アフィンな塔の隣接射は twisted 方程式の右平行移動。 -/
lemma affineTower_step (x : ∀ n, G n) (n : ℕ) (a : G (n + 1)) :
    (affineTower G q x).map (homOfLE (Nat.le_succ n)).op a = q n a * (x n)⁻¹ := by
  dsimp only [affineTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- 合成したアフィンな遷移も元の合成した準同型の右平行移動。 -/
lemma affineTower_map (x : ∀ n, G n) (i j : ℕ) (hij : i ≤ j) :
    ∃ c : G i, ∀ a : G j,
      (affineTower G q x).map (homOfLE hij).op a =
        transition G q (homOfLE hij).op a * c := by
  induction j, hij using Nat.le_induction with
  | base =>
    refine ⟨1, fun a ↦ ?_⟩
    simp [transition]
    rfl
  | succ j hij ih =>
    obtain ⟨c, hc⟩ := ih
    let h : op j ⟶ op i := (homOfLE hij).op
    let g : op (j + 1) ⟶ op j := (homOfLE (Nat.le_succ j)).op
    have he : (homOfLE (hij.trans (Nat.le_succ j))).op = g ≫ h := Subsingleton.elim _ _
    refine ⟨(transition G q h) ((x j)⁻¹) * c, fun a ↦ ?_⟩
    rw [he, Functor.map_comp, transition_comp]
    change (affineTower G q x).map h ((affineTower G q x).map g a) =
      (transition G q h) ((transition G q g) a) *
        ((transition G q h) ((x j)⁻¹) * c)
    rw [affineTower_step, hc, map_mul, ← mul_assoc]
    have hg (a : G (j + 1)) : transition G q g a = q j a := by
      dsimp only [transition]
      rw [groupTower_step]
      rfl
    rw [hg]

end
end SerrePositivity.InfinityCategories.Kan.TowerLimOne

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.affineTower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.affineTower := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.affineTower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.affineTower_map := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.affineTower_map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.affineTower_step := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.affineTower_step

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.groupTower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.groupTower := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.groupTower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.groupTower_step := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.groupTower_step

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.transition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.transition := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.transition

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.transition_comp := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.transition_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.TowerLimOne.transition.eq_1 := _root_.SerrePositivity.InfinityCategories.Kan.TowerLimOne.transition.eq_1
