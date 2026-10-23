module

public import SerrePositivity.InfinityCategories.F1.Categories.QCatDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianStrictTransportEquivalence

/-!
概要：通常の小圏の nerve 上の一般の cocartesian fibration に、Cat∞ 値の実際の図式を与える。
方針：F1B の cocartesian section の strict transport を QCat 値に束ね、coherent nerve へ実現する。
規約：図式の対象での fiber 比較は同じ恒等射評価。全 fibration の分類同値はまだ主張しない。
使われ方：Cat∞ 値 straightening の通常圏の nerve 上の分類図式の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_quasicategory_of_innerFibration

/-- cocartesian section による元の strict transport を、小さい quasicategory 値の関手に束ねる。 -/
def cocartesianStrictTransportQCatFunctor {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [InnerFibration p] : C ⥤ QCat.{u} where
  obj c := ⟨kanCocartesianStrictTransport p c, inferInstance⟩
  map f := kanCocartesianStrictTransportMap p f
  map_id c := kanCocartesianStrictTransportMap_id p c
  map_comp f g := kanCocartesianStrictTransportMap_comp p f g

/-- 一般の cocartesian fibration の strict transport の、元の Cat∞ への coherent な実現。 -/
def cocartesianStrictTransportCoherentDiagram {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ CatInfinity.{u} :=
  qCatDiagramCoherentNerve (cocartesianStrictTransportQCatFunctor p)

/-- 実現した同じ図式は、各頂点で元の cocartesian section の quasicategory を表す。 -/
lemma cocartesianStrictTransportCoherentDiagram_vertex
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    (cocartesianStrictTransportCoherentDiagram p).app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex c)) =
    coherentNerveVertex ((cocartesianStrictTransportQCatFunctor p).obj c) :=
  qCatDiagramCoherentNerve_vertex _ _

/-- この同じ図式が表す quasicategory は、元の指定 fiber と恒等射評価で同値。 -/
def cocartesianStrictTransportCoherentDiagramFiberEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (c : C) :
    QCatEquivalence (coherentNerveObject
      ((cocartesianStrictTransportCoherentDiagram p).app (Opposite.op ⦋0⦌)
        (ULift.up (nerveVertex c)))).obj (vertexFiber p (nerveVertex c)) := by
  rw [cocartesianStrictTransportCoherentDiagram_vertex, coherentNerveObject_vertex]
  exact kanCocartesianStrictTransportFiberEquivalence p c

end SerrePositivity.InfinityCategories
