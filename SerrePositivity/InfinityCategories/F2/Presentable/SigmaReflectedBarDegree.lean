module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorAdjunction
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaRepresentableCoproductInd
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointCoconePreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarDegreeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiagramColimitTransport

/-!
概要：全前層の元の bar の各次数を専用反映で Ind 対象へ送る。
方針：反映の小余積保存と同じ可逆 Yoneda 単位で表現可能小余積へ比較する。
規約：構成済みの元の bar と同じ反映を合成する。
使われ方：反映した元の bar の simplicial Ind 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：元の全前層 bar に同じ反映を適用した各項は Ind に属する。
方針：同じ次数の小余積余錐を反映し、可逆 Yoneda 単位で小表現可能図式へ戻す。
規約：各項を別の bar の選択へ取り替えない。
使われ方：元の bar の反映から simplicial Ind 生成へ接続する。 -/
lemma sigmaReflector_barDegree_isInd {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {L : PresheafInfinity C ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (n : SmallSimplexOpposite.{u}) :
    IsIndVertex Cardinal.aleph0 C
      ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
        ((presheafBarObject F ≫ L).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex n)))) := by
  obtain ⟨c, hc, hv⟩ := presheafBarObject_degree_coproduct F n
  have hLc := mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    (sigmaReflectorAdjunction β hβ) c hc
  let p := nerveMap (presheafBarFiberInclusion F n.objDown.down) ≫
    nerveMap (presheafBarToTransport F) ≫ transportSimplexFirstVertexMap
      (smallRightUnstraightening F) ≫ smallRightUnstraighteningProjection F
  have hi := sigmaReflectorLeftKan_unit_isIso β hβ
  let e : FunctorIso (yonedaInfinityMap C ≫ L) (sigmaYonedaInfinityMap C) :=
    (asIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))).symm
  have e' : FunctorIso
      (((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (presheafBarFiberInclusion F n.objDown.down)) ≫ presheafBarInputDiagram F) ≫ L)
      ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) := by
    simpa only [p, presheafBarInputDiagram, presheafElementsYonedaDiagram,
      Functor.map_comp, Category.assoc] using e.precomp ((SSet.uliftFunctor.{u + 1, u}).map p)
  obtain ⟨d, hd, hdv⟩ := exists_colimitCocone_functorIso_sameVertex e' (mapJoinCocone L c) hLc
  have hh := sigmaYoneda_smallCoproduct_isInd hC p d hd
  rwa [hdv, mapJoinCocone_vertex, hv] at hh

end SerrePositivity.InfinityCategories.F2.Presentable
