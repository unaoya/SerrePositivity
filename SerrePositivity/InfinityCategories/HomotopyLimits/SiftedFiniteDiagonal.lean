module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.HomotopyLimits.CofinalTensor
public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedInfinity

/-!
概要：sifted な底から元の全有限非空反復積への対角は right cofinal。
方針：元の二項対角と、残りの元の反復対角との直積を合成する。
規約：n は因子数 n+1。底の quasicategory 性は仮定しない。
使われ方：HTT 5.5.8.11、余極限と全有限積の交換の非空の場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の底の n+1 個の反復積への、元の恒等射を全成分に持つ対角。 -/
def nonemptyFiniteDiagonal (B : SSet.{u}) :
    (n : ℕ) → B ⟶ nonemptyFiniteSSetProduct n (fun _ ↦ B)
  | 0 => 𝟙 B
  | n + 1 => lift (𝟙 B) (nonemptyFiniteDiagonal B n)

/-- 元の反復対角の各射影は厳密に元の恒等射。 -/
lemma nonemptyFiniteDiagonal_projection (B : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    nonemptyFiniteDiagonal B n ≫ nonemptyFiniteSSetProjection n (fun _ ↦ B) i = 𝟙 B := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [nonemptyFiniteDiagonal, nonemptyFiniteSSetProjection, eqToHom_refl,
      Category.comp_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact lift_fst _ _
    · change lift (𝟙 B) (nonemptyFiniteDiagonal B n) ≫ (_ ≫ _) = _
      rw [← Category.assoc, lift_snd, ih]

/-- sifted な底の元の有限非空反復対角は、全因子数で right cofinal。 -/
lemma nonemptyFiniteDiagonal_isRightCofinal (B : SSet.{u}) [IsSiftedInfinity B] (n : ℕ) :
    IsRightCofinal (nonemptyFiniteDiagonal B n) := by
  induction n with
  | zero => exact isRightCofinal_id B
  | succ n ih =>
    have h := (IsSiftedInfinity.diagonal_rightCofinal (K := B)).comp
      (isRightCofinal_whiskerLeft ih B)
    have he : lift (𝟙 B) (𝟙 B) ≫ (B ◁ nonemptyFiniteDiagonal B n) =
        nonemptyFiniteDiagonal B (n + 1) := by
      rw [lift_whiskerLeft, Category.id_comp]
      rfl
    rwa [he] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
