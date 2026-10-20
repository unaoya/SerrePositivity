module

public import SerrePositivity.InfinityCategories.F2.CoconeFiberValueMap
public import SerrePositivity.InfinityCategories.F2.CoherentTotalCoconeUnit
public import SerrePositivity.InfinityCategories.F2.UliftPrecomposition

/-!
概要：元の小さい単位の比較を大きい全空間の実際の写像へ戻す。
方針：内部 Hom の縮小同型の逆の頂点を計算し、元の単位比較を写す。
規約：元の余錐と単位を保持する。
使われ方：必要な fiber 標的への前合成の同値性を元の小さい単位で検証する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}

/-- 概要：縮小した内部 Hom の頂点を戻すと、元の射の持ち上げを縮小同型で前合成する。
方針：各次数で関手の値を比較する。
規約：標的の Kan 性は不要。使われ方：元の単位比較の頂点の計算。 -/
lemma smallUnstraighteningHomIso_inv_vertex
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) {Z : SSet.{u}}
    (a : smallLeftUnstraightening F ⟶ Z) :
    (smallUnstraighteningHomIso F Z).inv.app (Opposite.op ⦋0⦌) (ULift.up (functorVertex a)) =
      functorVertex ((smallLeftUnstraighteningIso F).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map a) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  rfl

/-- 概要：元の単位を大きい全空間からの実際の射として表示する。
方針：縮小同型の逆と元の単位の持ち上げを続ける。
規約：元の単位を使う。使われ方：元の余錐の値への写像の比較先。 -/
def coherentLargeTotalUnit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :=
  (smallLeftUnstraighteningIso F).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (coherentDiagramTotalUnit F)

/-- 概要：元の全空間余錐の値への写像は大きい全空間からの元の単位と関手同型。
方針：保存済みの単位の頂点同型を縮小した内部 Hom の逆で写す。
規約：指定頂点の厳密な等式を保持。使われ方：全 Hom の前合成の比較。 -/
def coherentLargeTotalCoconeUnitIso
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :
    FunctorIso (coconeFiberValueMapAt (coherentDiagramTotalCocone F)
      (coherentDiagramTotalVertex F) (coherentDiagramTotalCocone_vertex F))
      (coherentLargeTotalUnit F) := by
  have e := (coherentTotalCoconeUnitIso F).map
    (smallUnstraighteningHomIso F (spaceInfinityObject (coherentDiagramTotalVertex F)).obj).inv
  rw [coconeFiberValueMapAt_smallComparison, smallUnstraighteningHomIso_inv_vertex] at e
  exact e

/-- 概要：大きい全空間の単位の小さい Kan 標的の持ち上げへの前合成は同値。
方針：元の小さい単位の前合成同値を内部 Hom の宇宙同型で移す。
規約：検査標的の宇宙を明示。使われ方：native な余錐の全 fiber Hom の判定。 -/
lemma coherentLargeTotalUnit_pre_homotopyEquivalence
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    (Z : SSet.{u}) [KanComplex Z] :
    IsSimplicialHomotopyEquivalence
      ((pre (coherentLargeTotalUnit F)).app ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  rw [coherentLargeTotalUnit, pre_map, NatTrans.comp_app]
  have h := (isPrecompositionEquivalence_of_iso (smallLeftUnstraighteningIso F).symm)
    ((SSet.uliftFunctor.{u + 1, u}).obj Z)
  exact (ulift_pre_homotopyEquivalence _
    (coherentDiagramTotalUnit_pre_homotopyEquivalence F Z)).comp h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
