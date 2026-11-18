module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFunctorEdge
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：指定したHomの同じ代表へのunstraighteningの作用は、相対同型まで合成を保つ。
方針：三つの指定辺のHomの合成式から三角形を取り、既存の辺の作用の合成則を適用する。
規約：Kerodon Remark 5.6.2.18（Tag 0271）、HTT §3.3.2の既存構成の合成法則。
  結論は元の二射そのものの相対頂点の同型で、別の比較射を選び直さない。
使われ方：5∞-1の残り第2項の証明分割、元の復元射と任意の表現の接続。
-/

@[expose] public noncomputable section
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
/-- 同じ指定Homの合成の作用は、二つの同じ作用の合成と底上で同型。 -/
lemma unstraighteningFunctorHom_comp_iso {B : SSet.{u}}
    {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (a : FunctorHom F G) (b : FunctorHom G J) :
    Nonempty (VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom (a ≫ b)) (unstraighteningFunctorHom_projection _))
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom a ≫ unstraighteningFunctorHom b)
        (by rw [Category.assoc, unstraighteningFunctorHom_projection,
          unstraighteningFunctorHom_projection]))) := by
  have hEdge {U V : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
      (c : FunctorHom U V) :
      VertexIso
        (relativeFunctorVertex (leftUnstraighteningProjection V) (leftUnstraighteningProjection U)
          (leftUnstraighteningEdgeMap U V (smallUnstraighteningHomEdge c)).val
          (leftUnstraighteningEdgeMap U V (smallUnstraighteningHomEdge c)).property)
        (relativeFunctorVertex (leftUnstraighteningProjection V) (leftUnstraighteningProjection U)
          (unstraighteningFunctorHom c) (unstraighteningFunctorHom_projection c)) := by
    refine leftUnstraighteningMappingSpaceMap_edgeVertexIso U V (smallUnstraighteningHomEdge c) ≪≫
      (eqToIso (congrArg HomotopyCategory.mk ?_)).symm
    exact leftUnstraighteningMappingVertexMap_vertex U V (smallUnstraighteningHomParameter c)
  let ea := smallUnstraighteningHomEdge a
  let eb := smallUnstraighteningHomEdge b
  let ec := smallUnstraighteningHomEdge (a ≫ b)
  obtain ⟨s⟩ := compStruct_nonempty_of_homMk_fac
    (show Truncated.HomotopyCategory.homMk ea.toTruncated ≫
      Truncated.HomotopyCategory.homMk eb.toTruncated =
      Truncated.HomotopyCategory.homMk ec.toTruncated by
      rw [smallUnstraighteningHomEdge_hom, smallUnstraighteningHomEdge_hom,
        smallUnstraighteningHomEdge_hom])
  let ss : SSet.Edge.CompStruct ea eb ec := SSet.Edge.CompStruct.ofTruncated s
  let A := leftUnstraighteningEdgeMap F G ea
  let D := leftUnstraighteningEdgeMap G J eb
  have ep : VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (A.val ≫ D.val) (by rw [Category.assoc, D.property, A.property]))
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom a ≫ D.val)
        (by rw [Category.assoc, D.property, unstraighteningFunctorHom_projection])) := by
    simpa only [relativeFunctorPost_vertex] using
      (hEdge a).map (relativeFunctorPost (leftUnstraighteningProjection G)
        (leftUnstraighteningProjection J) D.val D.property (leftUnstraighteningProjection F))
  have eq : VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom a ≫ D.val)
        (by rw [Category.assoc, D.property, unstraighteningFunctorHom_projection]))
      (relativeFunctorVertex (leftUnstraighteningProjection J) (leftUnstraighteningProjection F)
        (unstraighteningFunctorHom a ≫ unstraighteningFunctorHom b)
        (by rw [Category.assoc, unstraighteningFunctorHom_projection,
          unstraighteningFunctorHom_projection])) := by
    let ov : Over.mk (leftUnstraighteningProjection F) ⟶
        Over.mk (leftUnstraighteningProjection G) :=
      Over.homMk (unstraighteningFunctorHom a) (unstraighteningFunctorHom_projection a)
    let e0 := (hEdge b).map (relativeFunctorOverPre (leftUnstraighteningProjection J) ov)
    have hl := relativeFunctorOverPre_vertex (leftUnstraighteningProjection J) ov D.val D.property
    have hr := relativeFunctorOverPre_vertex (leftUnstraighteningProjection J) ov
      (unstraighteningFunctorHom b) (unstraighteningFunctorHom_projection b)
    exact (eqToIso (congrArg HomotopyCategory.mk hl)).symm ≪≫ e0 ≪≫
      eqToIso (congrArg HomotopyCategory.mk hr)
  exact ⟨(hEdge (a ≫ b)).symm ≪≫ leftUnstraighteningEdgeMap_compositionIso ss ≪≫ ep ≪≫ eq⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
