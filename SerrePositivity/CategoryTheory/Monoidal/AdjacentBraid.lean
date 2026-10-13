module

public import SerrePositivity.CategoryTheory.Monoidal.AdjacentTranspositions

/-!
# 隣接交換の braid 関係

三因子の Yang–Baxter 恒等式を、残りの反復テンソルとの積へ延長する。
括弧付けの比較により、先頭の二つの隣接交換へ接続する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 三因子の最初の隣接交換。 -/
def tripleFirstHom (X : C) : X ⊗ (X ⊗ X) ⟶ X ⊗ (X ⊗ X) :=
  (α_ X X X).inv ≫ (β_ X X).hom ▷ X ≫ (α_ X X X).hom

/-- 三因子の二番目の隣接交換。 -/
def tripleSecondHom (X : C) : X ⊗ (X ⊗ X) ⟶ X ⊗ (X ⊗ X) := X ◁ (β_ X X).hom

/-- 三因子を一つのブロックとしてから尾と合わせた括弧付けの比較。 -/
def tripleTailIso (X : C) (n : ℕ) :
    (X ⊗ (X ⊗ X)) ⊗ power X n ≅ power X (n + 3) :=
  (α_ X (X ⊗ X) (power X n)) ≪≫ whiskerLeftIso X (α_ X X (power X n))

@[reassoc] lemma tripleTail_first (X : C) (n : ℕ) :
    (tripleFirstHom X ▷ power X n) ≫
        (tripleTailIso X n).hom =
      (tripleTailIso X n).hom ≫ (swapFirstIso X (n + 1)).hom := by
  dsimp [tripleTailIso, swapFirstIso, tripleFirstHom, tripleSecondHom, power]
  simp only [whiskerLeftIso_hom, whiskerRightIso_hom]
  monoidal

@[reassoc] lemma tripleTail_second (X : C) (n : ℕ) :
    (tripleSecondHom X ▷ power X n) ≫ (tripleTailIso X n).hom =
      (tripleTailIso X n).hom ≫ (X ◁ (swapFirstIso X n).hom) := by
  dsimp [tripleTailIso, swapFirstIso, tripleFirstHom, tripleSecondHom, power]
  simp only [whiskerLeftIso_hom, whiskerRightIso_hom]
  monoidal

/-- 先頭の二つの隣接交換は braid 関係を満たす。 -/
lemma swapFirstIso_braid (X : C) (n : ℕ) :
    (swapFirstIso X (n + 1)).hom ≫ (X ◁ (swapFirstIso X n).hom) ≫
      (swapFirstIso X (n + 1)).hom =
    (X ◁ (swapFirstIso X n).hom) ≫ (swapFirstIso X (n + 1)).hom ≫
      (X ◁ (swapFirstIso X n).hom) := by
  apply (cancel_epi (tripleTailIso X n).hom).mp
  have hcore : tripleFirstHom X ≫ tripleSecondHom X ≫ tripleFirstHom X =
      tripleSecondHom X ≫ tripleFirstHom X ≫ tripleSecondHom X := by
    simpa only [tripleFirstHom, tripleSecondHom, Category.assoc] using yang_baxter X X X
  have h := congrArg (fun f ↦ (f ▷ power X n) ≫ (tripleTailIso X n).hom) hcore
  simp only [comp_whiskerRight, Category.assoc] at h
  rw [tripleTail_first, tripleTail_second_assoc, tripleTail_first_assoc,
    tripleTail_second, tripleTail_first_assoc, tripleTail_second_assoc] at h
  exact h

/-- 任意の隣接した二つの交換は braid 関係を満たす。 -/
lemma adjacentIso_braid (X : C) (n : ℕ) (i : Fin n) :
    (adjacentIso X (n + 1) i.castSucc).hom ≫ (adjacentIso X (n + 1) i.succ).hom ≫
      (adjacentIso X (n + 1) i.castSucc).hom =
    (adjacentIso X (n + 1) i.succ).hom ≫ (adjacentIso X (n + 1) i.castSucc).hom ≫
      (adjacentIso X (n + 1) i.succ).hom := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact swapFirstIso_braid X n
    · change (X ◁ (adjacentIso X (n + 1) j.castSucc).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.succ).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.castSucc).hom) =
      (X ◁ (adjacentIso X (n + 1) j.succ).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.castSucc).hom) ≫
        (X ◁ (adjacentIso X (n + 1) j.succ).hom)
      simpa only [whiskerLeft_comp] using congrArg (fun f ↦ X ◁ f) (ih j)

end SerrePositivity.TensorPowers
