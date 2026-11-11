module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFaceBlockHomology

/-!
概要：正の番号の面のホモロジー係数は H(G) の同じ始点係数の恒等射である。
方針：端点の等号射の自然性と実面ブロックの shift 比較を合成する。
規約：等号輸送を保持してから係数の恒等性を導く。
使われ方：非退化ホモロジー bar の正の面との比較。
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

lemma dgCoherentBarVertexHomologyTransport_eq (x : D) (r : ℤ)
    {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D} (hMN : M = N) (j : J)
    (hM : M = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm j))
    (hN : N = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G (nerveEquiv.symm j)) :
    HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)) hMN))) r ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r N j hN).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r M j hM).hom := by
  cases hMN
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    Category.id_comp]

lemma dgCoherentBarSignedFaceHomologyDiagram {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceCochain R D G s i x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceCochain_closed R D G s i x) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x (q + ((n : ℤ) + 1))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ)) (s.obj 0)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).trans
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G (n + 1) s))).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s).hom := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedFaceHomology, Category.assoc,
    dgCoherentBarVertexHomologyTransport_eq R D G x (q + ((n : ℤ) + 1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).symm (s.obj 0)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G (n + 1) s)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_face_succ R D G s i).trans
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G (n + 1) s))]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
