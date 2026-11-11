module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitValueAction
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningValueOverPre
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSquarePostOverPreEvaluation

/-!
概要：元の二面比較の値への像を、同じ底上の射の前合成と整合させる。
方針：二面比較の制限での値の保持と、相対 Hom の値への作用の厳密な自然性を合成する。
規約：元の全係数・指定値を保持。使われ方：三角形の三辺の比較を同じ全空間で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) {C E : SSet.{u + 1}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
  (p : C ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B)
  (d : E ⟶ (SSet.uliftFunctor.{u + 1, u}).obj B) (t : E ⟶ C) (ht : t ≫ p = d)
local notation "z" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "R₀" => relativeFunctorOverPre (leftUnstraighteningProjection F)
  (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
local notation "R₃" => relativeFunctorOverPre (leftUnstraighteningProjection (SSet.const z :
  (CategoryTheory.Functor.obj SSet.uliftFunctor B) ⟶ SpaceInfinity))
  (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
local notation "Qp" => Iso.hom (constantUnstraighteningRelativeIso p z) ≫
  CategoryTheory.Functor.map (ihom C) (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "Qd" => Iso.hom (constantUnstraighteningRelativeIso d z) ≫
  CategoryTheory.Functor.map (ihom E) (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "V" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (KanObject.obj (spaceInfinityObject z))

/-- 値へ写した元の二面比較は、同じ底上の射による前合成後も同じ指定値を持つ。 -/
lemma coherentColimitUnitValueAction_overPre_heq
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F) p) _⦋0⦌) :
    HEq (VertexIso.map (coherentColimitUnitValueAction B H p x) ((pre t).app V))
      (coherentColimitUnitValueAction B H d ((R₀).app _ x)) := by
  unfold coherentColimitUnitValueAction
  refine (heq_of_eq (vertexIso_map_comp (coherentColimitUnitValueComparison B H p x)
    Qp ((pre t).app V))).trans ?_
  refine (vertexIso_map_heq (coherentColimitUnitValueComparison B H p x)
    (constantUnstraighteningRelativeIso_value_overPre p d t ht z).symm).trans ?_
  refine (heq_of_eq (vertexIso_map_comp (coherentColimitUnitValueComparison B H p x)
    R₃ Qd)).symm.trans ?_
  exact functorSquareSequentialPostComparison_overPre_app_map_heq
    (coherentColimitUnitUpperTriangle B H) (coherentColimitUnitLowerTriangle B H) p d t ht x Qd

end SerrePositivity.InfinityCategories.F2
