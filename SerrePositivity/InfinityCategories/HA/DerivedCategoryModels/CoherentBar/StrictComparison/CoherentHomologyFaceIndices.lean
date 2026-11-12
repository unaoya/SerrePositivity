module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFaceHomologyDiagram
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarNondegFaces

/-!
概要：面の始点ラベルと、同じ頂点ホモロジー同型の添字等号の自然性。
方針：nerve の面の頂点公式と、等号射に対する関手の単位則を使う。
規約：通常の bar の各面係数と同じ始点添字を使う。
使われ方：層ホモロジーの個別係数比較を bar の面写像へ合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgCoherentBarFace_first_succ {J : Type u} [Category.{u} J] {n : ℕ}
    (s : (nerve J) _⦋n + 1⦌) (i : Fin (n + 1)) :
    ((nerve J).δ i.succ s).obj 0 = s.obj 0 := by
  rw [nerve.δ_obj, Fin.succ_succAbove_zero]

lemma dgCoherentBarFace_first_zero {J : Type u} [Category.{u} J] {n : ℕ}
    (s : (nerve J) _⦋n + 1⦌) :
    ((nerve J).δ (0 : Fin (n + 2)) s).obj 0 = s.obj (⟨1, by omega⟩ : Fin (n + 2)) := by
  rw [nerve.δ_obj, Fin.succAbove_zero]
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarVertexHomologyTransport_index (x : D) (r : ℤ) (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    {j k : J} (hjk : j = k)
    (hM : M = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm j))
    (hN : M = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm k)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r M j hM).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r).map (eqToHom hjk) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r M k hN).hom := by
  cases hjk
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

lemma dgCoherentBarSourceHomologyIso_positiveFace {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) (r : ℤ) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x r n ((nerve J).δ i.succ s)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r).map
        (eqToHom (dgCoherentBarFace_first_succ s i)) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)) (s.obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).trans
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G (n + 1) s))).hom :=
  dgCoherentBarVertexHomologyTransport_index R D G x r
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)) (dgCoherentBarFace_first_succ s i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G n ((nerve J).δ i.succ s)) _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
