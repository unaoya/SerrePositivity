module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyEdges
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeColumns
public import SerrePositivity.DifferentialGraded.Module.HomCycles

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarSource_vertex (s : I _⦋0⦌) :
    dgCoherentBarSource R D G ⟨0, s⟩ = coherentDiagramVertex G s := by
  simp only [dgCoherentBarSource, SimplexCategory.const_eq_id, op_id]
  erw [I.map_id]
  rfl

def dgCoherentBarVertexInclusion (s : I _⦋0⦌) :
    ForgetEnrichment.of (Complex R) (coherentDiagramVertex G s) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) := by
  let hMC := dgCoherentBarMaurerCartan_unconditional R D G
  let z := dgCoherentBarNativeColumn R D G hMC ⟨0, s⟩
  let f := moduleMorphismOfCycle R D
    (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨0, s⟩))
    (N := ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G))
    z (dgCoherentBarNativeColumn_vertex_closed R D G hMC s)
  exact eqToHom (congrArg (ForgetEnrichment.of (Complex R))
    (dgCoherentBarSource_vertex R D G s).symm) ≫ f

def dgCoherentBarVertexHomologyMap (x : D) (q : ℤ) (s : I _⦋0⦌) :
    ((coherentDiagramVertex G s).obj (Opposite.op x)).homology q ⟶
      ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q :=
  HomologicalComplex.homologyMap
    ((moduleEvaluation R D x).map (dgCoherentBarVertexInclusion R D G s)) q

end SerrePositivity.InfinityCategories
