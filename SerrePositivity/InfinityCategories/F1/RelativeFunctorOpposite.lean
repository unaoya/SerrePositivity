module

public import SerrePositivity.InfinityCategories.F1.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.F1.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.Stable.VertexFiberOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.FibersBaseIso

/-!
概要：相対関手空間の単体順序の反転は、反転した射影と図式の相対関手空間と同型。
方針：fiber の反転、底の内部 Hom 同型、全空間の内部 Hom 同型を順に合成する。
規約：底上の射の向きは変えず、パラメーターの単体順序だけを反転する。
使われ方：right fibrations の元の相対 Hom を left fibrations の相対 Hom へ比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 反転した元の相対 Hom と、反転した同じ射影・図式の相対 Hom の厳密な同型。 -/
def relativeFunctorOppositeIso {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (relativeFunctorSpace p a).op ≅
      relativeFunctorSpace (SSet.opFunctor.map p) (SSet.opFunctor.map a) := by
  let b := SSet.opObjEquiv.symm (functorVertex a)
  let eB := HomotopyLimits.oppositeInternalHomIso A B
  let eE := HomotopyLimits.oppositeInternalHomIso A E
  let r := SSet.opFunctor.map ((ihom A).map p)
  let s := (ihom A.op).map (SSet.opFunctor.map p)
  have he : eE.hom ≫ s = r ≫ eB.hom :=
    (HomotopyLimits.oppositeInternalHom_post A p).symm
  exact vertexFiberOpIso ((ihom A).map p) (functorVertex a) ≪≫
    HomotopyLimits.vertexFiberBaseIso r eB b ≪≫
    vertexFiberIsoOfTotalIso (r ≫ eB.hom) s eE he (eB.hom.app _ b) ≪≫
    eqToIso (congrArg (vertexFiber s) (oppositeInternalHomIso_vertex a))

/-- fiber の頂点の等式による移送は、同じ全空間への包含を保つ。 -/
lemma vertexFiber_eqToIso_ι {E B : SSet.{u}} (p : E ⟶ B)
    {b c : B _⦋0⦌} (h : b = c) :
    (eqToIso (congrArg (vertexFiber p) h)).hom ≫ vertexFiberι p c = vertexFiberι p b := by
  cases h
  exact Category.id_comp _

/-- この相対 Hom の反転同型は、内部 Hom への包含の後で標準反転比較となる。 -/
lemma relativeFunctorOppositeIso_hom_ι {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    (relativeFunctorOppositeIso p a).hom ≫
      vertexFiberι ((ihom A.op).map (SSet.opFunctor.map p))
        (functorVertex (SSet.opFunctor.map a)) =
    SSet.opFunctor.map (vertexFiberι ((ihom A).map p) (functorVertex a)) ≫
      (HomotopyLimits.oppositeInternalHomIso A E).hom := by
  unfold relativeFunctorOppositeIso
  simp only [Iso.trans_hom, Category.assoc]
  dsimp only [vertexFiberIsoOfTotalIso]
  rw [vertexFiber_eqToIso_ι _ (oppositeInternalHomIso_vertex a)]
  rw [vertexFiberMap_ι]
  rw [← Category.assoc _ _ (HomotopyLimits.oppositeInternalHomIso A E).hom,
    HomotopyLimits.vertexFiberBaseIso_hom_ι]
  rfl

end SerrePositivity.InfinityCategories
