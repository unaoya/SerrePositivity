module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroLayerNativeColumn
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.UniversalMapColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ZeroShiftIn

/-!
概要：native 零次元列を実閉射へ戻し、零次元層の各包含との関係を示す。
方針：閉零 cycle の同値と零 shift の単位・余単位を用いる。
規約：元の指定余錐の零次元係数を保つ。
使われ方：指定 native 増大のホモロジーを各脚で照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgBarNativeVertexModuleMap (s : I _⦋0⦌) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G) :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D G (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G) ⟨0, s⟩)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn_vertex_closed R D G
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G) s)

lemma dgBarNativeVertexModuleMap_cycle (s : I _⦋0⦌) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgBarNativeVertexModuleMap R D G s))).val =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D G (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G) ⟨0, s⟩ :=
  _root_.SerrePositivity.DifferentialGraded.moduleMorphismOfCycle_cycle R D _ _

def dgBarCoconeVertexModuleMap (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (s : I _⦋0⦌) :=
  dgBarNativeVertexModuleMap R D G s ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeUniversalMap R D G (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan_unconditional R D G) c

lemma dgBarCoconeVertexModuleMap_cycle (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G) (s : I _⦋0⦌) :
    (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (dgBarCoconeVertexModuleMap R D G c s))).val = _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeColumn R D G c ⟨0, s⟩ := by
  rw [dgBarCoconeVertexModuleMap, ← _root_.SerrePositivity.DifferentialGraded.moduleHomCycle_postcompose,
    dgBarNativeVertexModuleMap_cycle]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarCoconeUniversalMap_columns R D G c ⟨0, s⟩

lemma dgBarZeroLayerInclusion_ι (s : I _⦋0⦌) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G 0) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerIndex s) ≫
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion R D G =
      (moduleShiftZeroIsoObj R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩)).hom ≫
        dgBarNativeVertexModuleMap R D G s := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext q
  let L := Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G 0) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerIndex s) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion R D G
  let σ := moduleShiftZeroIsoObj R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩)
  have h := congrArg (fun z : (moduleHom R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G)).X 0 =>
      (moduleHomπ R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G) x).f 0 z)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarZeroLayerInclusion_nativeColumn R D G s)
  erw [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerLeft_apply_π] at h
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftIn_zero R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨0, s⟩),
    ← _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain R D x σ.inv] at h
  have hn := _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain R D x (dgBarNativeVertexModuleMap R D G s)
  rw [dgBarNativeVertexModuleMap_cycle] at hn
  erw [← hn] at h
  have hq := congrArg (fun z => z.v q q (add_zero q)) h
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hq
  have hσ := congrArg (fun f => ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map f).f q) σ.hom_inv_id
  simp only [Functor.map_comp, HomologicalComplex.comp_f,
    CategoryTheory.Functor.map_id, HomologicalComplex.id_f] at hσ
  conv_rhs => rw [Functor.map_comp, HomologicalComplex.comp_f]
  change ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map L).f q =
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map σ.hom).f q ≫
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (dgBarNativeVertexModuleMap R D G s)).f q
  calc
    _ = (((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map σ.hom).f q ≫
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map σ.inv).f q) ≫
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map L).f q := by rw [hσ, Category.id_comp]
    _ = _ := by rw [Category.assoc, hq]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
