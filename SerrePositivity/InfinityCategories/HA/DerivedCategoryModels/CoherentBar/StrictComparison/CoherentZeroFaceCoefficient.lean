module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEqualities

/-!
概要：一次 prefix の実係数を零番の面の同じ頂点係数へ輸送する。
方針：raw 後尾ラベルの等号を shift と頂点ホモロジーへ送り、元の辺射へ合わせる。
規約：通常の bar と同じ零番の面の係数射を右辺に保持する。
使われ方：一次ホモロジー微分の全交代面和の同定。
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

lemma dgCoherentBarSignedZeroFaceCoefficient {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixCochain R D G s x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixCochain_closed R D G s x) q ≫
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarTail_one_eq_face_zero s)))) (q + 1) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s (0 : Fin (n + 2)))).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) n
        ((nerve J).δ (0 : Fin (n + 2)) s)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))).map
          (s.map (homOfLE (Fin.zero_le ((0 : Fin (n + 2)).succAbove 0)))) := by
  let r := q + ((n : ℤ) + 1)
  let F := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r
  let h0 := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarTail_one_eq_face_zero s
  let hs := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G) h0
  let hj := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFace_first_zero s).symm
  let g := s.map (homOfLE (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))
  let g0 := s.map (homOfLE (Fin.zero_le ((0 : Fin (n + 2)).succAbove 0)))
  have hg : g ≫ eqToHom hj = g0 := Subsingleton.elim _ _
  let A := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixCochain R D G s x)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixCochain_closed R D G s x) q
  let D0 := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x r n
    ((nerve J).δ (0 : Fin (n + 2)) s)).hom
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by omega))).obj (Opposite.op x))
    (n : ℤ) (q + 1) r (by dsimp only [r]; omega)).hom
  have hm := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFamilyShiftHomology_transport R D G h0 x (q + 1) r
    (by dsimp only [r, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail]; simp only [Nat.add_sub_cancel]; omega)
    (by dsimp only [r, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace]; omega)
  have hv := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransport_equalities R D G x r hs hj
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_firstTail_nerve R D G s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G n ((nerve J).δ (0 : Fin (n + 2)) s))
  have h1 := congrArg (fun f => A ≫ f ≫ D0) hm
  have h2 := congrArg (fun f => A ≫ T ≫ f) hv
  have h3 := congrArg (fun f => f ≫ F.map (eqToHom hj))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixHomologyDiagram R D G s x q)
  simp only [Category.assoc] at h1 h2 h3
  have hh := h1.trans (h2.trans h3)
  change _ = _ ≫ _ ≫ F.map g ≫ F.map (eqToHom hj) at hh
  rw [← F.map_comp, hg] at hh
  exact hh

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
