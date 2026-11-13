module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.NonemptyFiniteSSetProduct

/-!
概要：元の有限非空反復積の普遍射と、元の全射影による一意性。
方針：元の二項積の持ち上げを反復し、元の射影で厳密に照合する。
規約：元の因子・射・添字を保持する。
使われ方：元の全空間 Kan 模型の全有限 native 積錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の n+1 個の射を元の反復積への一つの射にまとめる。 -/
def nonemptyFiniteSSetLift : (n : ℕ) → {E : Fin (n + 1) → SSet.{u}} → {A : SSet.{u}} →
    ((i : Fin (n + 1)) → A ⟶ E i) → (A ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n E)
  | 0, _, _, f => f 0
  | n + 1, _, _, f => lift (f 0) (nonemptyFiniteSSetLift n (fun i ↦ f i.succ))

/-- 元の反復持ち上げの各射影は元の射そのもの。 -/
lemma nonemptyFiniteSSetLift_projection (n : ℕ) {E : Fin (n + 1) → SSet.{u}}
    {A : SSet.{u}} (f : (i : Fin (n + 1)) → A ⟶ E i) (i : Fin (n + 1)) :
    nonemptyFiniteSSetLift n f ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n E i = f i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [nonemptyFiniteSSetLift, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection, eqToHom_refl,
      Category.comp_id]
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact lift_fst _ _
    · change lift _ _ ≫ (_ ≫ _) = _
      rw [← Category.assoc, lift_snd, ih]

/-- 元の反復積への二射は元の全射影への合成が一致すれば等しい。 -/
lemma nonemptyFiniteSSetProduct_hom_ext (n : ℕ) (E : Fin (n + 1) → SSet.{u})
    {A : SSet.{u}} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct n E}
    (h : ∀ i, f ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n E i =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n E i) : f = g := by
  induction n with
  | zero =>
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection, eqToHom_refl, Category.comp_id] using h 0
  | succ n ih =>
    apply CartesianMonoidalCategory.hom_ext
    · exact h 0
    · apply ih
      intro i
      simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection, Fin.cases_succ, Category.assoc] using h i.succ

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
