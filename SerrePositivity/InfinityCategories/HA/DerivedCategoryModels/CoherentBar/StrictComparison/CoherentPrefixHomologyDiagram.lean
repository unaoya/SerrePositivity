module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentVertexHomologyTransport

/-!
概要：一次 prefix の実ホモロジー係数を H(G) の関手の辺へ同定する。
方針：閉零加群射の等号から頂点ホモロジーの自然性を使い、shift 比較へ合成する。
規約：元の coherent 図式と実 prefix 係数を保持する。
使われ方：非退化 bar の零番の面との微分比較。
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

def dgCoherentBarSourceHomologyIso (x : D) (r : ℤ) (n : ℕ) (s : (nerve J) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n, s⟩).obj (Opposite.op x)).homology r ≅
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r).obj (s.obj 0) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n, s⟩)
    (s.obj 0) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G n s)

lemma dgCoherentBarPrefixHomologyDiagram_naturality {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (x : D) (r : ℤ) :
    HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle R D
        (M := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩))
        (N := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by omega))))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D G s 0 (by omega))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarPrefixZeroHom_closed R D G s))) r ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x r
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by omega)))
        (s.obj (⟨1, by omega⟩ : Fin (n + 2))) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_firstTail_nerve R D G s)).hom =
    (dgCoherentBarSourceHomologyIso R D G x r (n + 1) s).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r).map (s.map (homOfLE
        (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransport_naturality R D G x r
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_nerve R D G (n + 1) s) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_firstTail_nerve R D G s)
    _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarPrefixCycle_eq_diagramEdge R D G s)

lemma dgCoherentBarSignedPrefixHomologyDiagram {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixCochain R D G s x)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixCochain_closed R D G s x) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by omega))).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarVertexHomologyTransportIso R D G x (q + ((n : ℤ) + 1))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 (by omega)))
        (s.obj (⟨1, by omega⟩ : Fin (n + 2))) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSource_firstTail_nerve R D G s)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s).hom ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))).map (s.map (homOfLE
          (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSignedPrefixHomology, Category.assoc,
    dgCoherentBarPrefixHomologyDiagram_naturality]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
