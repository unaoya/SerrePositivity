module

public import SerrePositivity.KST.LocalizingInvariants.RawFiberConeMap
public import SerrePositivity.KST.LocalizingInvariants.StrictConeHomotopyRestriction

/-!
概要：置換前の実 BF fiber 比較を、元の cospan と頂点射を保つ coherent な全錐比較にする。
方針：通常の全錐自然変換を strict coherent prism へ写す。
規約：頂点射・cospan の全区間を保持。使われ方：置換した fiber の比較との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.LocalizingInvariants.RawFiberComparison

local instance rawCubeSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def cube : SSet.Homotopy (FiberModel.infinityCone p).val (FiberModel.infinityCone q).val :=
  StrictConeMap.homotopy (diagramMap p q a b h) _ _ (map p q a b h)
    (cone_condition p q a b h)

lemma cube_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (cube p q a b h)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] _))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (map p q a b h)).edge :=
  StrictConeMap.homotopy_apex _ _ _ _ _

lemma cube_base :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) _ ▷ (Δ[1] : SSet.{u + 1})) ≫
        (cube p q a b h).h =
      (β_ ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (AsSmall.{u} WalkingCospan))) Δ[1]).hom ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.strictCoherentNatTransMap (diagramMap p q a b h) :=
  StrictConeMap.homotopy_base _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.RawFiberComparison
