module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftKanHomMapPostcomposition

/-!
概要：同じ表現の族から得たpointedな比較と分類図式の比較は、元の射影の下で一致する。
方針：同じtransportWitnessDiagram_conditionをホモトピー圏へ送り、端点の表示の移送を消す。
規約：Kerodon §5.6（Tag 027M）、HTT §3.3.2の既存構成の射影・係数移送の法則。
  二つの比較を独立に選ばず、同じ表現空間内の頂点同型を使う。
使われ方：S8 の指定unstraightening比較における全空間側と分類図式側の照合。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 同じ表現空間の指定同型から得た二つの比較の射は、元の射影の下で両立する。 -/
lemma LeftTransportRepresentation.pointedIso_projection
    {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (R S : LeftTransportRepresentation p)
    (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    kanFunctorHomCongr
      (U := R.pointedMap ≫ pointedSpaceProjection.{u})
      (V := S.pointedMap ≫ pointedSpaceProjection.{u})
      (U' := p ≫ R.diagram) (V' := p ≫ S.diagram)
      R.pointedMap_projection S.pointedMap_projection
      (postcomposeFunctorHom (F := R.pointedMap) (G := S.pointedMap)
        pointedSpaceProjection.{u} (R.pointedIso S h).hom) =
      precomposeFunctorHom p (R.diagramIso S h).hom := by
  have hp : (hoFunctor.map (transportWitnessPointed p)).toFunctor ⋙
      (hoFunctor.map ((ihom E).map pointedSpaceProjection.{u})).toFunctor =
      (hoFunctor.map (transportWitnessDiagram p)).toFunctor ⋙
        (hoFunctor.map ((pre p).app SpaceInfinity.{u})).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp, transportWitnessDiagram_condition,
      Functor.map_comp, Cat.Hom.comp_toFunctor]
  have hm := congrArg Arrow.mk (Functor.congr_hom hp h.hom)
  simp only [Functor.comp_map, Arrow.arrow_mk_comp_eqToHom,
    Arrow.arrow_mk_eqToHom_comp] at hm
  apply Arrow.mk_injective _ _
  simpa only [postcomposeFunctorHom_eq_map, precomposeFunctorHom_eq_map,
    kanFunctorHomCongr, Iso.homCongr_apply,
    LeftTransportRepresentation.pointedIso, LeftTransportRepresentation.diagramIso,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    VertexIso.map, Functor.mapIso_hom, Functor.map_comp, eqToHom_map,
    Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp] using hm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
