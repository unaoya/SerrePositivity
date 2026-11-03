module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
public import SerrePositivity.InfinityCategories.Core.FunctorComposition
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Universe.Kan
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberValueMap
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.LargeTotalCoconeUnit

/-!
概要：元の全空間余錐の fiber 写像による、小さい Kan 値への前合成同値。
方針：元の単位との比較と、頂点 fiber の値への同値の前合成を消去する。
規約：指定した余錐と元の単位を保持。使われ方：native な輸送作用から元の頂点射を回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 概要：元の余極限頂点の fiber から指定頂点の元の値への比較。
方針：頂点の厳密な等式と値の回収を続ける。
規約：元の比較を使用。使われ方：native な輸送の始域表示。 -/
def coherentTotalSourceValueMap :
    vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (coherentDiagramTotalVertex F)).obj :=
  eqToHom (congrArg (vertexFiber pointedSpaceProjection) (coherentDiagramTotalCocone_vertex F)) ≫
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex F)).hom

/-- 概要：元の余極限頂点の fiber の値への比較は同値。
方針：頂点の等式の同型と元の fiber の同値。
規約：元の比較射。使われ方：前合成比較の消去。 -/
lemma coherentTotalSourceValueMap_isQCatEquivalence :
    IsQCatEquivalence (coherentTotalSourceValueMap F) := by
  let e := eqToIso (congrArg (vertexFiber pointedSpaceProjection)
    (coherentDiagramTotalCocone_vertex F))
  have h := (qCatEquivalenceOfIso e).isQCatEquivalence
  exact h.comp (pointedSpaceFiberValueEquivalence
    (coherentDiagramTotalVertex F)).isQCatEquivalence

/-- 概要：元の余錐の fiber 写像による任意の小さい Kan 値の持ち上げへの前合成は同値。
方針：元の単位との指定同型と fiber の値比較の前合成同値を消去。
規約：検査する標的の宇宙を明示。使われ方：元の native な射の値の反映。 -/
lemma coherentTotalCoconeFiber_value_pre_homotopyEquivalence
    (Z : SSet.{u}) [KanComplex Z] :
    IsSimplicialHomotopyEquivalence
      ((pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
        ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  let V := (SSet.uliftFunctor.{u + 1, u}).obj Z
  have hU := coherentLargeTotalUnit_pre_homotopyEquivalence F Z
  have e := (coherentLargeTotalCoconeUnitIso F).map_pre V
  have hd := (hU.isQCatEquivalence.ofFunctorIso e.symm).isSimplicialHomotopyEquivalence
  change IsSimplicialHomotopyEquivalence
    ((pre (coconeFiberMap (coherentDiagramTotalCocone F) ≫
      coherentTotalSourceValueMap F)).app V) at hd
  rw [pre_map, NatTrans.comp_app] at hd
  have hr := (coherentTotalSourceValueMap_isQCatEquivalence F).precompose V
  exact hr.isSimplicialHomotopyEquivalence.cancel_left hd

end SerrePositivity.InfinityCategories.F2
