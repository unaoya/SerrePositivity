module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.NativeVertexModuleMaps
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ClosedHomTransport

/-!
概要：native 余錐から回収した零次元頂点射は、同じ一単体の閉零射。
方針：端点の移送と零次元列の cycle を照合する。
規約：元の余錐の同じ実一単体を使う。
使われ方：余錐のホモロジー脚との一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgBarCoconeVertexRecovered (c : JoinCocone G) (s : I _⦋0⦌) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨0, s⟩) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarCoconeModule R D G c) :=
  eqToHom (congrArg (ForgetEnrichment.of (Complex R))
      (dgCoherentBarCoconeSimplex_source R D G c s).symm) ≫
    (dgCoherentBarCoconeSimplex R D G c s).edgeClosed 0 (Fin.last (0 + 1)) (by decide) ≫
      eqToHom (congrArg (ForgetEnrichment.of (Complex R))
        (dgCoherentBarCoconeSimplex_last R D G c s))

lemma dgBarCoconeVertexRecovered_cycle (c : JoinCocone G) (s : I _⦋0⦌) :
    (closedHomEquiv R (RightModule R D) _ _ (dgBarCoconeVertexRecovered R D G c s)).val =
      dgCoherentBarCoconeColumn R D G c ⟨0, s⟩ := by
  dsimp only [dgBarCoconeVertexRecovered]
  erw [dgBarClosedHom_transport R D
    (dgCoherentBarCoconeSimplex_source R D G c s)
    (dgCoherentBarCoconeSimplex_last R D G c s)
    ((dgCoherentBarCoconeSimplex R D G c s).edgeClosed 0 (Fin.last (0 + 1)) (by decide))]
  simp only [Simplex.edgeClosed, Equiv.apply_symm_apply]
  change gradedHomTransport
    (dgCoherentBarCoconeSimplex_source R D G c s)
    (dgCoherentBarCoconeSimplex_last R D G c s) rfl
    ((dgCoherentBarCoconeSimplex R D G c s).edgeCycle 0 (Fin.last (0 + 1)) (by decide)).val = _
  dsimp only [dgCoherentBarCoconeColumn, Simplex.edgeCycle, Simplex.edgeHom]
  have hpair : ({0, Fin.last (0 + 1)} : Finset (Fin 2)) = Finset.univ := by decide
  congr 1

lemma dgBarCoconeVertexModuleMap_eq (c : JoinCocone G) (s : I _⦋0⦌) :
    dgBarCoconeVertexModuleMap R D G c s = dgBarCoconeVertexRecovered R D G c s := by
  apply (closedHomEquiv R (RightModule R D) _ _).injective
  apply Subtype.ext
  exact (dgBarCoconeVertexModuleMap_cycle R D G c s).trans
    (dgBarCoconeVertexRecovered_cycle R D G c s).symm

end SerrePositivity.InfinityCategories
