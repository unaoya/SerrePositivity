module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Unconditional

/-!
概要：実 dg 加群の strict 図式を、元の coherent bar の入力へ送る。
方針：通常の nerve の単体を閉零射の列として読み、高次成分零の包含を適用する。
規約：D-bar の既存の bar・正規化・微分は変更しない。
使われ方：filtered strict 余極限への標準射とその擬同型性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

def dgCoherentBarStrictDiagram :
    (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D) :=
  (show (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    nerve (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) from { app _ := ↾fun s => s.down ⋙ F }) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion R (RightModule R D)

lemma dgCoherentBarStrictDiagram_simplex {n : ℕ} (s : (nerve J) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex (dgCoherentBarStrictDiagram R D F) s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (s ⋙ F) := rfl

lemma dgCoherentBarStrictDiagram_vertex (s : (nerve J) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex (dgCoherentBarStrictDiagram R D F) s =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.obj 0)) := rfl

lemma dgCoherentBarStrictSource (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex (nerve J)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) s =
      ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (s.2.obj 0)) := rfl

lemma dgCoherentBarStrictTopRaw_eq_zero {n : ℕ} (hn : 0 < n)
    (s : (nerve J) _⦋n + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw (dgCoherentBarStrictDiagram R D F) s = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion_higher R (RightModule R D) (s ⋙ F)
    Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n)
    (by simp; omega) (by simp; omega)

lemma dgCoherentBarStrictTop_eq_zero {n : ℕ} (hn : 0 < n)
    (s : (nerve J) _⦋n + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop (dgCoherentBarStrictDiagram R D F) s = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop, dgCoherentBarStrictTopRaw_eq_zero R D F hn]
  exact map_zero _

abbrev dgCoherentBarStrictNormalizedModule : RightModule R D :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D (dgCoherentBarStrictDiagram R D F)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
