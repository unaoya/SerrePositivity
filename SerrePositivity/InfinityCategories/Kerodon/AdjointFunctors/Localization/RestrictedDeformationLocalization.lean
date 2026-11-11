module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RestrictedDeformationHomotopy
/-!
概要：変形による局所化を、包含の像を含む頂点全部分圏へ制限する。
方針：同じ辺条件と元の比較の持ち上げを、全標的の前合成同値へ渡す。
規約：全部分圏の対象を元の局所対象と同一視しない。使われ方：K-flat 入力の局所化。

対応節は Kerodon 6.3（Tag 01M4）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory SSet MonoidalClosed
open scoped _root_.Simplicial
/-- 元の辺条件を、指定写像の実一次単体に沿って引き戻す。 -/
def preimageEdges {A X : SSet.{u}} (j : A ⟶ X) (W : Set (X _⦋1⦌)) : Set (A _⦋1⦌) :=
  {s | j.app (Opposite.op ⦋1⦌) s ∈ W}
/-- 元の辺を反転する関手は、前合成後も引き戻した辺条件を反転する。 -/
lemma InvertsEdges.precomp {A X D : SSet.{u}} {L : X ⟶ D} {W : Set (X _⦋1⦌)}
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges L W) (j : A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (j ≫ L) (preimageEdges j W) := by
  intro s hs
  have hi := hL hs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := D)
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map (j ≫ L)))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (j.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map L)) rfl).mpr hi
variable {X D : SSet.{u}} (P : X _⦋0⦌ → Prop) (L : X ⟶ D) (I : D ⟶ X)
  (hI : ∀ x, P (I.app (Opposite.op ⦋0⦌) x)) (W : Set (X _⦋1⦌))
/-- 制限した包含と分解の合成は、元の同じ全関手同型で恒等に比較される。 -/
def deformationRestrictedRetractIso (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (I ≫ L) (𝟙 D)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P I hI ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ L)) (𝟙 D) := by
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using! e
/-- 制限した変形比較の各成分は、同じ引き戻し辺条件を満たす。 -/
lemma deformationRestrictedHomotopy_vertex_mem
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.deformationRestrictedHomotopy P L I hI H) x).edge ∈
      preimageEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι W := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.deformationRestrictedHomotopy P L I hI H) x).edge.val ∈ W
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.deformationRestrictedHomotopy_vertex_val]
  exact hH x.val
/-- 指定した全部分圏からの制限分解も、全反転関手 ∞ 圏との明示的前合成同値を与える。 -/
def deformationRestrictedLocalizationEquivalence
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges L W) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (I ≫ L) (𝟙 D))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W)
    (Y : SSet.{u}) [Quasicategory Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom D).obj Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet) Y
        (preimageEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι W) : SSet) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DeformationLocalization.deformationLocalizationPrecompositionEquivalence _ _ _
    (hL.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)
    (deformationRestrictedRetractIso P L I hI e)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.deformationRestrictedHomotopy P L I hI H)
    (deformationRestrictedHomotopy_vertex_mem P L I hI W H hH) Y
include hI in
/-- 包含の像を含む全部分圏からの同じ分解は、引き戻した辺に関する局所化。 -/
lemma isLocalization_of_restricted_deformation
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges L W) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (I ≫ L) (𝟙 D))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge ∈ W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ L)
      (preimageEdges (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι W) := by
  refine ⟨hL.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι, fun Y _ => ?_⟩
  exact (deformationRestrictedLocalizationEquivalence P L I hI W hL e H hH Y).isQCatEquivalence
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
