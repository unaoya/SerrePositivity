module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.Reindex
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# 添字圏の同値による重み付き錐空間の移送

概要：Hovey §5.4 の重み付き錐の同じ空間を添字の同値で比較する。
方針：各値のテンソルと前合成の可換性から右随伴の一意性を使う。
規約：モデル構造は不要で、元の図式と重みをともに同じ同値で移す。
使われ方：E 代数の右 frame の二重反対圏表示と元の始域 frame の錐の照合。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight

open _root_.CategoryTheory _root_.Functor _root_.CategoryTheory.Functor
open _root_.SerrePositivity.DiagramModel _root_.SerrePositivity.DiagramModel.WeightedCones

variable {J K : Type u} [SmallCategory J] [SmallCategory K] (e : J ≌ K)
  (W : K ⥤ SSet.{u})

/-- 概要：同値で重みを移した錐関手の比較（Hovey §5.4）。
方針：テンソルと前合成の合成随伴を元の錐の随伴と比較する。
規約：任意の移送先図式に自然な関手同型。
使われ方：元の重み付き錐の同じ単体集合を回収する。 -/
def coneSpaceReindexAuxIso :
    coneSpace J (e.functor ⋙ W) ≅
      (e.symm.congrLeft (E := SSet.{u})).inverse ⋙ coneSpace K W := by
  let adj := (WeightedCones.adjunction K W).comp (e.symm.congrLeft (E := SSet.{u})).toAdjunction
  let h : tensorDiagram K W ⋙ (e.symm.congrLeft (E := SSet.{u})).functor ≅
      tensorDiagram J (e.functor ⋙ W) := Iso.refl _
  exact Adjunction.rightAdjointUniq (WeightedCones.adjunction J (e.functor ⋙ W))
    (adj.ofNatIsoLeft h)

/-- 概要：図式と重みを同じ添字同値で移しても錐空間は同型（Hovey §5.4）。
方針：錐関手の比較と前合成同値の単位の逆を合成する。
規約：元の図式のすべての射に自然な実際の単体集合の同型。
使われ方：二重反対圏で作った右 frame の錐を元の添字へ戻す。 -/
def coneSpaceReindexIso :
    (e.symm.congrLeft (E := SSet.{u})).functor ⋙ coneSpace J (e.functor ⋙ W) ≅
      coneSpace K W :=
  isoWhiskerLeft _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.coneSpaceReindexAuxIso e W) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (e.symm.congrLeft (E := SSet.{u})).unitIso.symm (coneSpace K W) ≪≫
    Functor.leftUnitor _

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
