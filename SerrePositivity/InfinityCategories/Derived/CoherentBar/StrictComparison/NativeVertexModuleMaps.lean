module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroLayerNativeColumn
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.UniversalMapColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ZeroShiftIn

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgBarNativeVertexModuleMap (s : I _⦋0⦌) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨0, s⟩) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) :=
  moduleMorphismOfCycle R D
    (dgCoherentBarNativeColumn R D G (dgCoherentBarMaurerCartan_unconditional R D G) ⟨0, s⟩)
    (dgCoherentBarNativeColumn_vertex_closed R D G
      (dgCoherentBarMaurerCartan_unconditional R D G) s)

lemma dgBarNativeVertexModuleMap_cycle (s : I _⦋0⦌) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (dgBarNativeVertexModuleMap R D G s))).val =
      dgCoherentBarNativeColumn R D G (dgCoherentBarMaurerCartan_unconditional R D G) ⟨0, s⟩ :=
  moduleMorphismOfCycle_cycle R D _ _

def dgBarCoconeVertexModuleMap (c : JoinCocone G) (s : I _⦋0⦌) :=
  dgBarNativeVertexModuleMap R D G s ≫
    dgCoherentBarCoconeUniversalMap R D G (dgCoherentBarMaurerCartan_unconditional R D G) c

lemma dgBarCoconeVertexModuleMap_cycle (c : JoinCocone G) (s : I _⦋0⦌) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgBarCoconeVertexModuleMap R D G c s))).val = dgCoherentBarCoconeColumn R D G c ⟨0, s⟩ := by
  rw [dgBarCoconeVertexModuleMap, ← moduleHomCycle_postcompose,
    dgBarNativeVertexModuleMap_cycle]
  exact dgBarCoconeUniversalMap_columns R D G c ⟨0, s⟩

lemma dgBarZeroLayerInclusion_ι (s : I _⦋0⦌) :
    Sigma.ι (dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s) ≫
        dgBarZeroLayerInclusion R D G =
      (moduleShiftZeroIsoObj R D (dgCoherentBarSource R D G ⟨0, s⟩)).hom ≫
        dgBarNativeVertexModuleMap R D G s := by
  apply moduleMorphism_ext
  intro x
  apply HomologicalComplex.Hom.ext
  funext q
  let L := Sigma.ι (dgCoherentBarLayerFamily R D G 0) (dgBarZeroLayerIndex s) ≫
    dgBarZeroLayerInclusion R D G
  let σ := moduleShiftZeroIsoObj R D (dgCoherentBarSource R D G ⟨0, s⟩)
  have h := congrArg (fun z : (moduleHom R D (dgCoherentBarSource R D G ⟨0, s⟩)
      (dgCoherentBarNormalizedModuleUnconditional R D G)).X 0 =>
      (moduleHomπ R D (dgCoherentBarSource R D G ⟨0, s⟩)
        (dgCoherentBarNormalizedModuleUnconditional R D G) x).f 0 z)
    (dgBarZeroLayerInclusion_nativeColumn R D G s)
  erw [moduleHomWhiskerLeft_apply_π] at h
  erw [dgBarShiftIn_zero R D (dgCoherentBarSource R D G ⟨0, s⟩),
    ← moduleEvaluation_cochain R D x σ.inv] at h
  have hn := moduleEvaluation_cochain R D x (dgBarNativeVertexModuleMap R D G s)
  rw [dgBarNativeVertexModuleMap_cycle] at hn
  erw [← hn] at h
  have hq := congrArg (fun z => z.v q q (add_zero q)) h
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hq
  have hσ := congrArg (fun f => ((moduleEvaluation R D x).map f).f q) σ.hom_inv_id
  simp only [Functor.map_comp, HomologicalComplex.comp_f,
    CategoryTheory.Functor.map_id, HomologicalComplex.id_f] at hσ
  conv_rhs => rw [Functor.map_comp, HomologicalComplex.comp_f]
  change ((moduleEvaluation R D x).map L).f q =
    ((moduleEvaluation R D x).map σ.hom).f q ≫
      ((moduleEvaluation R D x).map (dgBarNativeVertexModuleMap R D G s)).f q
  calc
    _ = (((moduleEvaluation R D x).map σ.hom).f q ≫
        ((moduleEvaluation R D x).map σ.inv).f q) ≫
        ((moduleEvaluation R D x).map L).f q := by rw [hσ, Category.id_comp]
    _ = _ := by rw [Category.assoc, hq]

end SerrePositivity.InfinityCategories
