module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportRepresentationUnstraighteningComparison

/-!
概要：元の射の指定pointed同型を、指定分類同型の同じ代表辺に沿うprismへ戻す。
方針：既存の相対代表辺の変更を一度だけ適用し、元の同型の類と底の全prismを保持する。
規約：HTT §3.3.2、Kerodon Remark 5.6.2.18（Tag 0271）の既存構成の照合。
使われ方：R04で指定同型を保つ持ち上げとR04-PRを接続する短い証明分割。
-/

@[expose] public noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定pointed同型と同じ分類像を、元の指定分類辺を底とする全prismで表す。 -/
@[cite HTT "3.3.2" (partial := special) "元の指定同型を保つ相対代表辺の変更の法則。"]
lemma exists_transportRepresentation_arrowPrism_of_pointedIso {E F B : SSet.{u + 1}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q)
    (a : E ⟶ F) (ha : a ≫ q = p) (ν : FunctorIso R.diagram S.diagram)
    (P : FunctorIso R.pointedMap (a ≫ S.pointedMap))
    (hP : HEq (P.postcomp pointedSpaceProjection) (ν.precomp p)) :
    ∃ W : (Δ[1] : SSet.{u + 1}) ⊗ E ⟶ PointedSpaceInfinity.{u},
      prismEndpoint 0 E ≫ W = R.pointedMap ∧
      prismEndpoint 1 E ≫ W = a ≫ S.pointedMap ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫
        functorEdgePrism (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy
          (functorHomHomotopy ν.hom))) := by
  have hA : (a ≫ S.pointedMap) ≫ pointedSpaceProjection = p ≫ S.diagram := by
    rw [Category.assoc, S.pointedMap_projection, ← Category.assoc, ha]
  have hn : functorIsoOfEq (P.postcomp pointedSpaceProjection)
      R.pointedMap_projection hA = ν.precomp p :=
    eq_of_heq ((functorIsoOfEq_heq _ _ _).trans hP)
  let e := SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom))
  let r := e.toTruncated.map ((truncation 2).map ((pre p).app SpaceInfinity.{u}))
  have hr : Truncated.HomotopyCategory.homMk r = (ν.precomp p).hom := by
    change (SSet.mapHomotopyCategory ((pre p).app SpaceInfinity.{u})).map
      (Truncated.HomotopyCategory.homMk e.toTruncated) = _
    have he : Truncated.HomotopyCategory.homMk e.toTruncated = ν.hom :=
      functorHomHomotopy_hom _
    rw [he, functorIso_precomp_hom]
  obtain ⟨l, hl, _⟩ := functorIso_exists_edge_representative_over pointedSpaceProjection
    P (ν.precomp p) R.pointedMap_projection hA hn r hr
  refine ⟨functorEdgePrism (SSet.Edge.ofTruncated l),
    functorEdgePrism_zero _, functorEdgePrism_one _, ?_⟩
  have hx : SSet.yonedaEquiv.symm l.edge ≫ (ihom E).map pointedSpaceProjection =
      SSet.yonedaEquiv.symm e.edge ≫ (pre p).app SpaceInfinity.{u} := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm hl
  change functorFamilyPrism (SSet.yonedaEquiv.symm l.edge) ≫ pointedSpaceProjection = _
  rw [← functorFamilyPrism_post, hx, functorFamilyPrism_pre]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
