module
public import SerrePositivity.InfinityCategories.F1B.Localization.RestrictedDeformationLocalization
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatModuleNerve
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionLocalization
/-!
概要：右相対 K-flat 加群上の指定半自由分解も、実準同型辺に関する局所化。
方針：全加群の実変形比較を K-flat 頂点全部分圏へ制限し、同じ反転条件を使う。
規約：原 Hom の平坦性や全加群圏の Small 性は不要。
使われ方：通常 kernel tensor の実合成から、指定導来合成子の coherence を反映する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
/-- K-flat 入力に制限した、元の全加群の同じ指定半自由分解。 -/
def dgRelativeKFlatResolution :
    dgRelativeKFlatModuleNerve R E ⟶ dgModuleDerivedInfinityCategory R E :=
  dgRelativeKFlatModuleInclusion R E ≫
    dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))
/-- K-flat 全部分圏の実準同型辺は、元の実辺条件の引き戻し。 -/
def dgRelativeKFlatQuasiIsomorphismEdges : Set ((dgRelativeKFlatModuleNerve R E) _⦋1⦌) :=
  preimageEdges (dgRelativeKFlatModuleInclusion R E) (dgModuleQuasiIsomorphismEdges R E)
/-- K-flat 入力上の同じ指定分解は、実準同型辺を反転する。 -/
lemma dgRelativeKFlatResolution_invertsQuasiIsomorphismEdges :
    InvertsEdges (dgRelativeKFlatResolution R E) (dgRelativeKFlatQuasiIsomorphismEdges R E) :=
  (dgModuleResolution_invertsQuasiIsomorphismEdges R E).precomp
    (dgRelativeKFlatModuleInclusion R E)
/-- 同じ分解と半自由包含の合成から、K-flat 全部分圏上の恒等への実比較。 -/
def dgRelativeKFlatResolutionAugmentationHomotopy :
    SSet.Homotopy
      (dgRelativeKFlatResolution R E ≫ dgSemifreeToRelativeKFlatNerve R E)
      (𝟙 (dgRelativeKFlatModuleNerve R E)) :=
  deformationRestrictedHomotopy (dgModuleRelativeKFlatVertex R E) _ _
    (dgSemifreeModuleInclusion_vertex_relativeKFlat R E)
    (dgModuleResolutionAugmentationHomotopy R E)
/-- K-flat 入力上の同じ全単体 augmentation の各成分は、元の実準同型辺。 -/
lemma dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem
    (x : (dgRelativeKFlatModuleNerve R E) _⦋0⦌) :
    (simplicialHomotopyVertexEdge
      (dgRelativeKFlatResolutionAugmentationHomotopy R E) x).edge ∈
      dgRelativeKFlatQuasiIsomorphismEdges R E :=
  deformationRestrictedHomotopy_vertex_mem (dgModuleRelativeKFlatVertex R E) _ _
    (dgSemifreeModuleInclusion_vertex_relativeKFlat R E) _
    (dgModuleResolutionAugmentationHomotopy R E)
    (dgModuleResolutionAugmentationHomotopy_vertex_mem R E) x
/-- K-flat 入力上の指定分解の前合成は、任意標的の全反転関手圏との明示的同値。 -/
def dgRelativeKFlatResolutionLocalizationEquivalence (Y : SSet.{max (u + 1) v})
    [Quasicategory Y] :
    QCatEquivalence ((ihom (dgModuleDerivedInfinityCategory R E)).obj Y)
      (invertingFunctors (dgRelativeKFlatModuleNerve R E) Y
        (dgRelativeKFlatQuasiIsomorphismEdges R E) : SSet) :=
  deformationRestrictedLocalizationEquivalence (dgModuleRelativeKFlatVertex R E) _ _
    (dgSemifreeModuleInclusion_vertex_relativeKFlat R E) _
    (dgModuleResolution_invertsQuasiIsomorphismEdges R E) (dgModuleResolutionRetractIso R E)
    (dgModuleResolutionAugmentationHomotopy R E)
    (dgModuleResolutionAugmentationHomotopy_vertex_mem R E) Y
/-- K-flat 入力の元の指定半自由分解は、実準同型辺に関する ∞ 圏的局所化。 -/
lemma dgRelativeKFlatResolution_isLocalization :
    IsLocalization (dgRelativeKFlatResolution R E) (dgRelativeKFlatQuasiIsomorphismEdges R E) := by
  refine ⟨dgRelativeKFlatResolution_invertsQuasiIsomorphismEdges R E, fun Y _ => ?_⟩
  exact (dgRelativeKFlatResolutionLocalizationEquivalence R E Y).isQCatEquivalence
/-- K-flat 入力上の指定分解による前合成は、全写像空間上で充満忠実。 -/
lemma dgRelativeKFlatResolution_precomposition_isFullyFaithful
    (Y : SSet.{max (u + 1) v}) [Quasicategory Y] :
    IsFullyFaithful ((pre (dgRelativeKFlatResolution R E)).app Y) :=
  (dgRelativeKFlatResolution_isLocalization R E).precomposition_isFullyFaithful Y
end SerrePositivity.InfinityCategories
