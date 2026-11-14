module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationProduct
public import Mathlib.Data.Fin.Basic

/-!
概要：元の有限非空族の単体集合と射の反復積。
方針：最初の因子と残りの族を二項積し、元の各射影との可換性を回収する。
規約：添字 n は因子数 n+1。全因子と元の射を保持する。
使われ方：sifted 余極限と全有限積の交換の、元の全空間・底の模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- n+1 個の元の単体集合の反復積。 -/
def nonemptyFiniteSSetProduct : (n : ℕ) → (Fin (n + 1) → SSet.{u}) → SSet.{u}
  | 0, E => E 0
  | n + 1, E => E 0 ⊗ nonemptyFiniteSSetProduct n (fun i ↦ E i.succ)

/-- 反復積から元の i 番目の因子への射影。 -/
def nonemptyFiniteSSetProjection : (n : ℕ) → (E : Fin (n + 1) → SSet.{u}) →
    (i : Fin (n + 1)) → nonemptyFiniteSSetProduct n E ⟶ E i
  | 0, E, i => eqToHom (congrArg E (Fin.eq_zero i).symm)
  | n + 1, E, i => Fin.cases (fst (E 0) (nonemptyFiniteSSetProduct n (fun j ↦ E j.succ)))
      (fun j ↦ snd (E 0) (nonemptyFiniteSSetProduct n (fun k ↦ E k.succ)) ≫
        nonemptyFiniteSSetProjection n (fun k ↦ E k.succ) j) i

/-- 元の射の有限非空族の反復積射。 -/
def nonemptyFiniteSSetProductMap : (n : ℕ) → {E F : Fin (n + 1) → SSet.{u}} →
    ((i : Fin (n + 1)) → E i ⟶ F i) → (nonemptyFiniteSSetProduct n E ⟶
      nonemptyFiniteSSetProduct n F)
  | 0, _, _, f => f 0
  | n + 1, _, _, f => f 0 ⊗ₘ nonemptyFiniteSSetProductMap n (fun i ↦ f i.succ)

/-- 元の積射の i 番目の射影は、元の射影に元の i 番目の射を続けたもの。 -/
lemma nonemptyFiniteSSetProductMap_projection (n : ℕ) {E F : Fin (n + 1) → SSet.{u}}
    (f : (i : Fin (n + 1)) → E i ⟶ F i) (i : Fin (n + 1)) :
    nonemptyFiniteSSetProductMap n f ≫ nonemptyFiniteSSetProjection n F i =
      nonemptyFiniteSSetProjection n E i ≫ f i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [nonemptyFiniteSSetProductMap, nonemptyFiniteSSetProjection, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact tensorHom_fst _ _
    · change (_ ⊗ₘ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ _
      rw [← Category.assoc, tensorHom_snd, Category.assoc, ih, ← Category.assoc]

/-- 元の各射影が left fibration なら、元の有限積射も left fibration。 -/
lemma nonemptyFiniteSSetProductMap_leftFibration (n : ℕ)
    {E F : Fin (n + 1) → SSet.{u}} (f : (i : Fin (n + 1)) → E i ⟶ F i)
    (hf : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f i)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (nonemptyFiniteSSetProductMap n f) := by
  induction n with
  | zero => exact hf 0
  | succ n ih =>
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (f 0) := hf 0
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (nonemptyFiniteSSetProductMap n (fun i ↦ f i.succ)) :=
      ih _ (fun i ↦ hf i.succ)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibration_tensorHom _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
