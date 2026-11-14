module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.NonemptyFiniteSSetProduct

/-!
分割で生成：docstring を書き直すこと
概要：sifted な底から元の全有限非空反復積への対角は right cofinal。
方針：元の二項対角と、残りの元の反復対角との直積を合成する。
規約：n は因子数 n+1。底の quasicategory 性は仮定しない。
使われ方：HTT 5.5.8.11、余極限と全有限積の交換の非空の場合。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 元の底の n+1 個の反復積への、元の恒等射を全成分に持つ対角。 -/
def nonemptyFiniteDiagonal (B : SSet.{u}) :
    (n : ℕ) → B ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n (fun _ ↦ B)
  | 0 => 𝟙 B
  | n + 1 => lift (𝟙 B) (nonemptyFiniteDiagonal B n)

/-- 元の反復対角の各射影は厳密に元の恒等射。 -/
lemma nonemptyFiniteDiagonal_projection (B : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    nonemptyFiniteDiagonal B n ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun _ ↦ B) i = 𝟙 B := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [nonemptyFiniteDiagonal, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection, eqToHom_refl,
      Category.comp_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact lift_fst _ _
    · change lift (𝟙 B) (nonemptyFiniteDiagonal B n) ≫ (_ ≫ _) = _
      rw [← Category.assoc, lift_snd, ih]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
