module
public import SerrePositivity.InfinityCategories.Kan.DoubleMappingCylinderDesc
public import SerrePositivity.InfinityCategories.Kan.CartesianEdgeInterchange
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans

/-! # 二重円筒を横断する指定頂点の辺
概要：共通の中間選択を通る円筒の辺を作り、定数な評価で恒等辺を回収する。
方針：指定頂点の恒等辺と標準区間の辺の直積を円筒へ写す。
規約：円筒の左右の像の頂点を厳密に端点に使う。
使われ方：自然性パラメーター内の延長側・中間・逆射側の三辺の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Comparison SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 中間の指定頂点を通って左から右へ横断する円筒の辺。 -/
def doubleCylinderMiddleEdge {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) (c : C _⦋0⦌) :
    (doubleMappingCylinder f g).Edge
      ((doubleMappingCylinder_left f g).app _ (f.app _ c))
      ((doubleMappingCylinder_right f g).app _ (g.app _ c)) := by
  let e := cartesianEdgePair (SSet.Edge.id c) (SSet.Edge.ofTruncated homotopyIntervalEdge)
  refine (e.map (doubleMappingCylinder_middle f g)).ofEq ?_ ?_
  · exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (doubleMappingCylinder_zero f g) (Opposite.op ⦋0⦌)) c
  · exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (doubleMappingCylinder_one f g) (Opposite.op ⦋0⦌)) c

/-- 中央の円筒上で時刻によらない評価は、横断する辺を同じ頂点の恒等辺へ写す。 -/
lemma doubleCylinderMiddleEdge_constant_evaluation {C A B K : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (F : doubleMappingCylinder f g ⟶ K) (k : C ⟶ K)
    (h : doubleMappingCylinder_middle f g ≫ F = fst C (Δ[1] : SSet.{u}) ≫ k)
    (c : C _⦋0⦌) :
    ((doubleCylinderMiddleEdge f g c).map F).edge = (SSet.Edge.id (k.app _ c)).edge := by
  have hh := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋1⦌))
    (cartesianEdgePair (SSet.Edge.id c) (SSet.Edge.ofTruncated homotopyIntervalEdge)).edge
  change ((doubleCylinderMiddleEdge f g c).map F).edge = k.app _ (C.σ 0 c) at hh
  exact hh.trans (ConcreteCategory.congr_hom (k.naturality (SimplexCategory.σ (0 : Fin 1)).op) c)

/-- 円筒横断辺を任意のパラメーター比較へ送り、合成射の端点で表す。 -/
def doubleCylinderMiddleMappedEdge {C A B N : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (G : doubleMappingCylinder f g ⟶ N)
    (c : C _⦋0⦌) :
    N.Edge ((f ≫ doubleMappingCylinder_left f g ≫ G).app _ c)
      ((g ≫ doubleMappingCylinder_right f g ≫ G).app _ c) :=
  ((doubleCylinderMiddleEdge f g c).map G).ofEq rfl rfl

/-- 比較後に評価しても、中央部分が定数なら横断辺の像は恒等辺。 -/
lemma doubleCylinderMiddleMappedEdge_constant_evaluation {C A B N K : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) (G : doubleMappingCylinder f g ⟶ N)
    (F : N ⟶ K) (k : C ⟶ K)
    (h : doubleMappingCylinder_middle f g ≫ (G ≫ F) = fst C (Δ[1] : SSet.{u}) ≫ k)
    (c : C _⦋0⦌) :
    ((doubleCylinderMiddleMappedEdge f g G c).map F).edge =
      (SSet.Edge.id (k.app _ c)).edge :=
  doubleCylinderMiddleEdge_constant_evaluation f g (G ≫ F) k h c

end SerrePositivity.KST.SConstruction
