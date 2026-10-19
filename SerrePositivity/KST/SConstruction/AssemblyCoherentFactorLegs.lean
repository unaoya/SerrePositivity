module
public import SerrePositivity.KST.SConstruction.AssemblyCoherentObjectChoices
public import SerrePositivity.KST.SConstruction.AssemblyInputIdentityTransport
public import SerrePositivity.KST.SConstruction.ContractibleKanTriangles

/-! # 全選択から得る元の混合選択空間の自然性の二脚
概要：同じ coherent な全選択から源・標的の値を中央の値へ結ぶ二つの辺を得る。
方針：over 圏の辺の始点を恒等成分の比較と元の両端移送で付け直す。
規約：元の自然性の辺を指定しても、同じ二脚との比較三角形を保持する。
使われ方：全射列の選択と既存の因子の自然性・合成三角形の厳密な接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 同じ全選択の延長の値を中央へ結ぶ、元の両端移送を始点とする辺。 -/
def kanAssemblyCoherentSourceEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌)
    {X Y : I} (f : X ⟶ Y) :=
  diagramSelectionTransportEdge (kanAssemblyCoherentFamily r F v) (assemblyArrowFromSource f)
    (kanAssemblyInputIdentityChoicesIso r F X) (kanAssemblyMixedFromSource r (F.map f))
    (kanAssemblyInputIdentityChoicesIso_source r F f)

/-- 同じ全選択の延長の値を中央へ結ぶ、元の両端移送を始点とする辺。 -/
def kanAssemblyCoherentTargetEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌)
    {X Y : I} (f : X ⟶ Y) :=
  diagramSelectionTransportEdge (kanAssemblyCoherentFamily r F v) (assemblyArrowFromTarget f)
    (kanAssemblyInputIdentityChoicesIso r F Y) (kanAssemblyMixedFromTarget r (F.map f))
    (kanAssemblyInputIdentityChoicesIso_target r F f)

/-- 同じ全選択の逆射の値を中央へ結ぶ、元の両端移送を始点とする辺。 -/
def oneDirectionInverseCoherentSourceEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    {X Y : I} (f : X ⟶ Y) :=
  diagramSelectionTransportEdge (oneDirectionInverseCoherentFamily r F v) (assemblyArrowFromSource f)
    (oneDirectionInverseInputIdentityChoicesIso r F X) (oneDirectionInverseMixedFromSource r (F.map f))
    (oneDirectionInverseInputIdentityChoicesIso_source r F f)

/-- 同じ全選択の逆射の値を中央へ結ぶ、元の両端移送を始点とする辺。 -/
def oneDirectionInverseCoherentTargetEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    {X Y : I} (f : X ⟶ Y) :=
  diagramSelectionTransportEdge (oneDirectionInverseCoherentFamily r F v) (assemblyArrowFromTarget f)
    (oneDirectionInverseInputIdentityChoicesIso r F Y) (oneDirectionInverseMixedFromTarget r (F.map f))
    (oneDirectionInverseInputIdentityChoicesIso_target r F f)

/-- 任意の指定した延長の自然性の辺は、同じ全選択の二脚と実三角形をなす。 -/
lemma kanAssemblyCoherentLegTriangle_nonempty {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌)
    {X Y : I} (f : X ⟶ Y)
    (e : ((kanAssemblyInputArrowDiagram r F).obj (assemblyArrowMk f)).Edge
      ((kanAssemblyMixedFromSource r (F.map f)).app (Opposite.op ⦋0⦌)
        ((kanAssemblyInputIdentityChoicesIso r F X).hom.app (Opposite.op ⦋0⦌)
          (diagramSelectionVertex (kanAssemblyCoherentFamily r F v) (assemblyArrowMk (𝟙 X)))))
      ((kanAssemblyMixedFromTarget r (F.map f)).app (Opposite.op ⦋0⦌)
        ((kanAssemblyInputIdentityChoicesIso r F Y).hom.app (Opposite.op ⦋0⦌)
          (diagramSelectionVertex (kanAssemblyCoherentFamily r F v) (assemblyArrowMk (𝟙 Y)))))) :
    Nonempty (SSet.Edge.CompStruct e (kanAssemblyCoherentTargetEdge r F v f)
      (kanAssemblyCoherentSourceEdge r F v f)) :=
  contractibleKan_nonempty_compStruct (kanAssemblyInputArrowDiagram_isContractibleKan r F (assemblyArrowMk f))
    e (kanAssemblyCoherentTargetEdge r F v f) (kanAssemblyCoherentSourceEdge r F v f)

/-- 任意の指定した逆射の自然性の辺は、同じ全選択の二脚と実三角形をなす。 -/
lemma oneDirectionInverseCoherentLegTriangle_nonempty {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌)
    {X Y : I} (f : X ⟶ Y)
    (e : ((oneDirectionInverseInputArrowDiagram r F).obj (assemblyArrowMk f)).Edge
      ((oneDirectionInverseMixedFromSource r (F.map f)).app (Opposite.op ⦋0⦌)
        ((oneDirectionInverseInputIdentityChoicesIso r F X).hom.app (Opposite.op ⦋0⦌)
          (diagramSelectionVertex (oneDirectionInverseCoherentFamily r F v) (assemblyArrowMk (𝟙 X)))))
      ((oneDirectionInverseMixedFromTarget r (F.map f)).app (Opposite.op ⦋0⦌)
        ((oneDirectionInverseInputIdentityChoicesIso r F Y).hom.app (Opposite.op ⦋0⦌)
          (diagramSelectionVertex (oneDirectionInverseCoherentFamily r F v) (assemblyArrowMk (𝟙 Y)))))) :
    Nonempty (SSet.Edge.CompStruct e (oneDirectionInverseCoherentTargetEdge r F v f)
      (oneDirectionInverseCoherentSourceEdge r F v f)) :=
  contractibleKan_nonempty_compStruct (oneDirectionInverseInputArrowDiagram_isContractibleKan r F (assemblyArrowMk f))
    e (oneDirectionInverseCoherentTargetEdge r F v f) (oneDirectionInverseCoherentSourceEdge r F v f)

end SerrePositivity.KST.SConstruction
