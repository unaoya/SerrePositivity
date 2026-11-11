module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEdges
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColumns
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-!
概要：元の各頂点加群から実正規化 coherent bar への閉零射。
方針：零単体の native 列の閉性を元の対象へ輸送する。
規約：native 余錐の普遍性は使わない。G は高次 HA 成分つきのまま。
使われ方：ホモロジー余錐の脚と標準比較の構成。
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
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarSource_vertex (s : I _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource, SimplexCategory.const_eq_id, op_id]
  erw [I.map_id]
  rfl

def dgCoherentBarVertexInclusion (s : I _⦋0⦌) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G s) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G) := by
  let hMC := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G
  let z := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D G hMC ⟨0, s⟩
  let f := _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle R D
    (M := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩))
    (N := ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G))
    z (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn_vertex_closed R D G hMC s)
  exact eqToHom (congrArg (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R))
    (dgCoherentBarSource_vertex R D G s).symm) ≫ f

def dgCoherentBarVertexHomologyMap (x : D) (q : ℤ) (s : I _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G s).obj (Opposite.op x)).homology q ⟶
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q :=
  HomologicalComplex.homologyMap
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgCoherentBarVertexInclusion R D G s)) q

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
