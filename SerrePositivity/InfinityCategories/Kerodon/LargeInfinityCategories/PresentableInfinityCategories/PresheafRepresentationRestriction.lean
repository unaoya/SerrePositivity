module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.YonedaWeightLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SpaceUniverseLimits

/-!
概要：反対前層圏上の小さい空間値関手から表現対象の候補と制限同型を構成する。
方針：反対 Yoneda 制限を前層と読み、全 Yoneda 評価比較を候補頂点で評価する。
規約：候補は元の宇宙の前層であり、大きい前層への置換ではない。
使われ方：連続な前層の表現可能性の右 Kan 比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：反対 Yoneda による制限を元の小さい底上の前層として読む。
方針：反転と宇宙持ち上げの標準同型を前合成する。
規約：値の宇宙 u と元の関手 F を保持する。
使われ方：表現対象の具体的な候補。 -/
def presheafRepresentationCandidate {A : SSet.{u}} [Quasicategory A]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} A).hom ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A) ≫ F

/-- 概要：前層の宇宙変更の指定頂点は同じ全関手の宇宙変更。
方針：内部 Hom の宇宙比較を同じ前層の頂点で評価する。
規約：頂点の等式として元の前層を回収する。
使われ方：全 Yoneda 比較の指定表現候補への評価。 -/
lemma presheafUniverseDiagram_vertex {A : SSet.{u}}
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram A).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex P)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 2, u + 1}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} A).inv ≫
          (SSet.uliftFunctor.{u + 2, u + 1}).map P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm.injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：指定候補の表現可能前層と元の関手の宇宙変更は反対 Yoneda 上で自然同型。
方針：元の全 Yoneda Hom 比較を候補で評価し、反転の宇宙比較の両逆を相殺する。
規約：両辺は元の全関手の制限そのもの。
使われ方：右 Kan 普遍性による全表現同型の構成。 -/
def presheafRepresentation_restrictionIso {A : SSet.{u}} [Quasicategory A]
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (presheafRepresentationCandidate F)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)) ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightDiagram_universeIso A).app
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (presheafRepresentationCandidate F)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram_vertex, presheafUniverseDiagram_vertex] at e
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso _ _ at e
  simpa only [presheafRepresentationCandidate, CategoryTheory.Functor.map_comp,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp] using e

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
