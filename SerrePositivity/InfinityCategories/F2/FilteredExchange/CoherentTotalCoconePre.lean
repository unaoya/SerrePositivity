module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LargeTotalCoconeUnit
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PrecompositionTargetComparison

/-!
概要：構成済み全空間余錐の fiber 写像の全 fiber 標的への前合成同値。
方針：元の単位との関手同型、元の値との同値、前合成の自然性を順に使う。
規約：検査標的の宇宙を保持して元の小さい単位から証明する。
使われ方：元の native な全空間余錐の余極限性の最終入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u}}

/-- 概要：元の全空間余錐の fiber 写像は必要な全 fiber 標的への前合成同値を持つ。
方針：単位の前合成同値を元の値への写像へ移し、fiber 比較の同値を消去する。
規約：元の余錐と単位を保持。使われ方：全 Hom による native 余極限性の検証。 -/
lemma coherentTotalCoconeFiber_pre_homotopyEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (z : SpaceInfinity.{u} _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      ((pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
        (vertexFiber pointedSpaceProjection z)) := by
  let c : JoinCocone F := coherentDiagramTotalCocone F
  let v : SpaceInfinity.{u} _⦋0⦌ := coherentDiagramTotalVertex F
  let h : c.vertex = v := coherentDiagramTotalCocone_vertex F
  let Z : SSet.{u + 1} :=
    (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject z).obj
  have hU := coherentLargeTotalUnit_pre_homotopyEquivalence F (spaceInfinityObject z).obj
  have e : FunctorIso ((pre (coconeFiberValueMapAt c v h)).app Z)
      ((pre (coherentLargeTotalUnit F)).app Z) :=
    (coherentLargeTotalCoconeUnitIso F).map_pre Z
  have hd : IsSimplicialHomotopyEquivalence
      ((pre (coconeFiberValueMapAt c v h)).app Z) :=
    (hU.isQCatEquivalence.ofFunctorIso e.symm).isSimplicialHomotopyEquivalence
  let r : vertexFiber pointedSpaceProjection c.vertex ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject v).obj :=
    eqToHom (congrArg (vertexFiber pointedSpaceProjection) h) ≫
      (pointedSpaceFiberValueEquivalence v).hom
  have heq := (qCatEquivalenceOfIso
    (eqToIso (congrArg (vertexFiber pointedSpaceProjection) h))).isQCatEquivalence
  have hr : IsQCatEquivalence r :=
    heq.comp (pointedSpaceFiberValueEquivalence v).isQCatEquivalence
  have hp : IsSimplicialHomotopyEquivalence ((pre (coconeFiberMap c)).app Z) := by
    have hrp := (hr.precompose Z).isSimplicialHomotopyEquivalence
    change IsSimplicialHomotopyEquivalence ((pre (coconeFiberMap c ≫ r)).app Z) at hd
    rw [pre_map, NatTrans.comp_app] at hd
    exact hrp.cancel_left hd
  exact pre_homotopyEquivalence_of_target_equivalence (coconeFiberMap c)
    (pointedSpaceFiberValueEquivalence z).hom
    (pointedSpaceFiberValueEquivalence z).isQCatEquivalence hp

end SerrePositivity.InfinityCategories.F2
