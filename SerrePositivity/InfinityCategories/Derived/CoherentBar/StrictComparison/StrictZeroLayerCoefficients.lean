module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentNaturalLayerHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictHomologyDiagram
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
概要：strict 図式の零次元層ホモロジーの係数同型を元の頂点へ戻す。
方針：零 shift の標準同型と、strict 頂点の定義上の一致を使う。
規約：一般 coherent 比較の自然な係数同型をそのまま特殊化する。
使われ方：strict 標準増大とホモロジー余錐の脚の一致。
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
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

lemma dgBarZeroShiftHomology (M : RightModule R D) (x : D) (q : ℤ) :
    (dgComplexShiftHomologyIso R (M.obj (Opposite.op x)) 0 q q (by omega)).hom =
      HomologicalComplex.homologyMap
        ((moduleEvaluation R D x).map (moduleShiftZeroIsoObj R D M).hom) q := by
  rw [moduleShiftZeroIsoObj_hom_eval]
  exact (HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) 0).shiftIso_zero_hom_app q _

lemma dgCoherentBarStrictSourceHomologyIso (x : D) (q : ℤ) (n : ℕ)
    (s : (nerve J) _⦋n⦌) :
    (dgCoherentBarSourceHomologyIso R D (dgCoherentBarStrictDiagram R D F) x q n s).hom =
      (dgCoherentBarHomologyDiagramObjIso R D (dgCoherentBarStrictDiagram R D F)
        x q (s.obj 0)).inv := by
  dsimp only [dgCoherentBarSourceHomologyIso, dgCoherentBarVertexHomologyTransportIso,
    Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyMapIso_hom,
    Functor.mapIso_hom, eqToIso.hom]
  change HomologicalComplex.homologyMap
    ((moduleEvaluation R D x).map (𝟙 (F.obj (s.obj 0)))) q ≫ _ = _
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id, Category.id_comp]

end SerrePositivity.InfinityCategories
