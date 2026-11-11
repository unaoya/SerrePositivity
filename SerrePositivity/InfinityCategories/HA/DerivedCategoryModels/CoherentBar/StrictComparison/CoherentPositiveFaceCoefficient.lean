module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyFaceIndices

/-!
概要：実符号つき正の面ブロックの係数は、通常の H(G) bar の同じ面係数と一致する。
方針：始点添字の等号射で比較し、同じ関手の実面係数へ戻す。
規約：通常の bar と同じ射を右辺に保持する。
使われ方：一次ホモロジー微分の面和の同定。
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
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarSignedPositiveFaceCoefficient {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceCochain R D G s i x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceCochain_closed R D G s i x) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) n
        ((nerve J).δ i.succ s)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))).map
          (s.map (homOfLE (Fin.zero_le (i.succ.succAbove 0)))) := by
  let F := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))
  let e := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFace_first_succ s i
  let p := F.map (eqToHom e)
  let g := s.map (homOfLE (Fin.zero_le (i.succ.succAbove 0)))
  have hg : g ≫ eqToHom e = 𝟙 (s.obj 0) := Subsingleton.elim _ _
  have hp : F.map g ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← F.map_comp, hg, F.map_id]
  letI : IsIso p := by dsimp only [p]; infer_instance
  rw [← cancel_mono p]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso_positiveFace, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceHomologyDiagram]
  change _ = _ ≫ _ ≫ F.map g ≫ p
  rw [hp, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
