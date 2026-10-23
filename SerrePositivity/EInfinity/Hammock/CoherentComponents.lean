module

public import SerrePositivity.InfinityCategories.F1.Coherent.HomOrdinary
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftPiZero
public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 豊穣 Hom の連結成分から coherent な辺の類への比較

概要：同じ Hom 成分の元の射は coherent nerve のホモトピー圏で一致する。
方針：実際の coherent Hom 比較と pinched Hom の連結成分を使う。
規約：通常圏・元の豊穣 Hom・指定された射を保持する。
使われ方：実 Kan hammock nerve 内の指定射の反転。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

lemma coherentEdge_homMk_eq_of_components {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f g : X ⟶ Y)
    (h : SSet.π₀.mk (SimplicialCategory.homEquiv' X Y f) =
      SSet.π₀.mk (SimplicialCategory.homEquiv' X Y g)) :
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated := by
  have hu := congrArg (UniverseLiftPiZero.up.{u, v} (SimplicialCategory.sHom X Y)) h
  have hm := congrArg (SSet.mapπ₀ (coherentHomComparison X Y)) hu
  have hp := congrArg (pinchedHomPiZeroToHom (coherentNerveVertex X)
    (coherentNerveVertex Y)) hm
  change SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _
    ((coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y f)))) =
      SSet.Truncated.HomotopyCategory.homMk (pinchedHomVertexEquiv _ _
        ((coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y g)))) at hp
  have hf : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y f))) =
      (coherentNerveEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary f
  have hg : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ (ULift.up (SimplicialCategory.homEquiv' X Y g))) =
      (coherentNerveEdge g).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary g
  exact (congrArg₂ Eq (congrArg SSet.Truncated.HomotopyCategory.homMk hf)
    (congrArg SSet.Truncated.HomotopyCategory.homMk hg)).mp hp


lemma coherentEdge_homMk_eq_of_homotopy {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f g : X ⟶ Y)
    (H : SSet.Homotopy (eHomEquiv SSet f) (eHomEquiv SSet g)) :
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated := by
  apply coherentEdge_homMk_eq_of_components f g
  have h := AnodyneHomotopy.map_homotopy_eq SSet.π₀Functor
    PiZeroLocalization.inverts_anodyne H
  exact congrArg (fun k : SSet.π₀ (MonoidalCategory.tensorUnit SSet.{u}) ⟶
    SSet.π₀ (SimplicialCategory.sHom X Y) ↦ k (SSet.π₀.mk PUnit.unit)) h

end SerrePositivity.EInfinity.Hammock
