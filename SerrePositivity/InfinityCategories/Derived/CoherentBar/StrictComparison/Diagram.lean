module
public import SerrePositivity.InfinityCategories.Derived.NerveInclusion
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D)

def dgCoherentBarStrictDiagram :
    (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgNerve R (RightModule R D) :=
  (show (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    nerve (ModuleCategory R D) from { app _ := ↾fun s => s.down ⋙ F }) ≫
    closedNerveInclusion R (RightModule R D)

lemma dgCoherentBarStrictDiagram_simplex {n : ℕ} (s : (nerve J) _⦋n⦌) :
    coherentDiagramSimplex (dgCoherentBarStrictDiagram R D F) s =
      closedNerveSimplex (s ⋙ F) := rfl

lemma dgCoherentBarStrictDiagram_vertex (s : (nerve J) _⦋0⦌) :
    coherentDiagramVertex (dgCoherentBarStrictDiagram R D F) s =
      ForgetEnrichment.to (Complex R) (F.obj (s.obj 0)) := rfl

lemma dgCoherentBarStrictSource (s : dgCoherentBarIndex (nerve J)) :
    dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) s =
      ForgetEnrichment.to (Complex R) (F.obj (s.2.obj 0)) := rfl

lemma dgCoherentBarStrictTopRaw_eq_zero {n : ℕ} (hn : 0 < n)
    (s : (nerve J) _⦋n + 1⦌) :
    coherentDiagramTopRaw (dgCoherentBarStrictDiagram R D F) s = 0 := by
  exact closedNerveInclusion_higher R (RightModule R D) (s ⋙ F)
    Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega) (by simp; omega)

lemma dgCoherentBarStrictTop_eq_zero {n : ℕ} (hn : 0 < n)
    (s : (nerve J) _⦋n + 1⦌) :
    coherentDiagramTop (dgCoherentBarStrictDiagram R D F) s = 0 := by
  rw [coherentDiagramTop, dgCoherentBarStrictTopRaw_eq_zero R D F hn]
  exact map_zero _

abbrev dgCoherentBarStrictNormalizedModule : RightModule R D :=
  dgCoherentBarNormalizedModuleUnconditional R D (dgCoherentBarStrictDiagram R D F)

end SerrePositivity.InfinityCategories
