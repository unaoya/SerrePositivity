module
public import SerrePositivity.InfinityCategories.F1B.Localization.DeformationLocalization
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionRetract
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedInvertsQuasiIso
/-!
概要：全 dg 加群の実 nerve から半自由模型への指定分解は、準同型に関する局所化。
方針：同じ実 augmentation と包含上の恒等比較から、全標的の前合成の同値を構成する。
規約：全加群圏の Small 性や元の Hom の平坦性を要求しない。
使われ方：指定の一般 kernel 比較の coherence を、全関手圏上で反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
open DGNerve.HomotopyComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
/-- 全 dg 加群の nerve の準同型辺は、元の閉準同型の実一次単体。 -/
def dgModuleQuasiIsomorphismEdges : Set ((dgModuleNerve R E) _⦋1⦌) :=
  {s | ∃ (M N : ClosedCategory R (RightModule R E)) (f : M ⟶ N),
    moduleQuasiIso R E f ∧ (dgClosedEdge R (RightModule R E) f).edge = s}
/-- 閉準同型の実辺を反転する条件は、準同型辺全体を反転する条件を与える。 -/
lemma dgModuleQuasiIsomorphismEdges_inverts {Y : SSet.{max (u + 1) v}}
    (q : dgModuleNerve R E ⟶ Y)
    (h : ∀ (M N : ClosedCategory R (RightModule R E)) (f : M ⟶ N),
      moduleQuasiIso R E f → IsInvertibleEdge
        ((dgClosedEdge R (RightModule R E) f).map ((truncation 2).map q))) :
    InvertsEdges q (dgModuleQuasiIsomorphismEdges R E) := by
  intro s hs
  obtain ⟨M, N, f, hf, rfl⟩ := hs
  exact (isInvertibleEdge_congr (X := Y)
    (e := (edgeOfSimplex (dgClosedEdge R (RightModule R E) f).edge).map
      ((truncation 2).map q))
    (f := (dgClosedEdge R (RightModule R E) f).map ((truncation 2).map q)) rfl).mpr
      (h M N f hf)
/-- 全加群の指定半自由分解は、元の全ての閉準同型辺を反転する。 -/
lemma dgModuleResolution_invertsQuasiIsomorphismEdges :
    InvertsEdges
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      (dgModuleQuasiIsomorphismEdges R E) := by
  apply dgModuleQuasiIsomorphismEdges_inverts R E
  intro M N f hf
  exact dgModuleResolvedInfinity_invertsQuasiIso R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) (dgClosedEdge R (RightModule R E) f)
    (by simpa only [dgClosedEdge_closed] using! hf)
/-- 全加群の指定分解と実包含の合成から、同じ恒等関手への全単体比較。 -/
def dgModuleResolutionAugmentationHomotopy :
    SSet.Homotopy
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)) ≫
        dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E))) (𝟙 (dgModuleNerve R E)) := by
  let H := dgModuleResolvedAugmentationHomotopy R (RightModule R E) E
    (DGFunctor.id (RightModule R E))
  exact { h := H.h
          h₀ := H.h₀
          h₁ := by simpa only [dgNerve.map_id] using! H.h₁
          rel := H.rel }
/-- 指定の全単体比較の各成分は、同じ実半自由分解の準同型辺。 -/
lemma dgModuleResolutionAugmentationHomotopy_vertex_mem (x : (dgModuleNerve R E) _⦋0⦌) :
    (simplicialHomotopyVertexEdge (dgModuleResolutionAugmentationHomotopy R E) x).edge ∈
      dgModuleQuasiIsomorphismEdges R E := by
  obtain ⟨M, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := RightModule R E)).symm.surjective x
  let Q := dgModuleOutputResolutionObject R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) M
  refine ⟨_, _, Q.augmentation, Q.quasiIso, ?_⟩
  exact (dgModuleResolvedAugmentationHomotopy_vertex_edge R (RightModule R E) E
    (DGFunctor.id (RightModule R E)) M).symm
/-- 指定分解の前合成は、任意標的の全反転関手 ∞ 圏との明示的同値。 -/
def dgModuleResolutionLocalizationEquivalence (Y : SSet.{max (u + 1) v})
    [Quasicategory Y] :
    QCatEquivalence ((ihom (dgModuleDerivedInfinityCategory R E)).obj Y)
      (invertingFunctors (dgModuleNerve R E) Y (dgModuleQuasiIsomorphismEdges R E) : SSet) :=
  deformationLocalizationPrecompositionEquivalence _ _ _
    (dgModuleResolution_invertsQuasiIsomorphismEdges R E) (dgModuleResolutionRetractIso R E)
    (dgModuleResolutionAugmentationHomotopy R E)
    (dgModuleResolutionAugmentationHomotopy_vertex_mem R E) Y
/-- 全加群の指定半自由分解は、実準同型辺に関する ∞ 圏的局所化。 -/
lemma dgModuleResolution_isLocalization :
    IsLocalization
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      (dgModuleQuasiIsomorphismEdges R E) := by
  refine ⟨dgModuleResolution_invertsQuasiIsomorphismEdges R E, fun Y _ => ?_⟩
  exact (dgModuleResolutionLocalizationEquivalence R E Y).isQCatEquivalence
end SerrePositivity.InfinityCategories
