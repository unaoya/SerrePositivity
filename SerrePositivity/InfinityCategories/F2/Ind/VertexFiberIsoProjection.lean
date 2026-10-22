module

public import SerrePositivity.InfinityCategories.F1.LeftTransportRepresentation
public import SerrePositivity.InfinityCategories.F1.PullbackFiber

/-!
概要：底の同型・頂点の等式・引き戻しによる fiber 同型の、元の全空間への射影を照合する。
方針：既存の fiber 同型の包含公式と、同型の往復則だけを使う。
規約：同じ射の合成を保持し、fiber ごとに比較射を選び直さない。
使われ方：section product scaffold の指定 fiber 比較を元の評価へ同定する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 全空間の底上の同型を fiber へ制限しても、元の同型の射を回収する。 -/
lemma vertexFiberIsoOfTotalIso_hom_ι {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (e : X ≅ Y) (he : e.hom ≫ q = p) (b : B _⦋0⦌) :
    (vertexFiberIsoOfTotalIso p q e he b).hom ≫ vertexFiberι q b =
      vertexFiberι p b ≫ e.hom := vertexFiberMap_ι p q e.hom he b

/-- 頂点の等式で移した fiber の包含は、元の全空間への包含そのもの。 -/
lemma vertexFiber_vertexEqToIso_ι {X B : SSet.{u}} (p : X ⟶ B)
    {b c : B _⦋0⦌} (h : b = c) :
    (eqToIso (congrArg (vertexFiber p) h)).hom ≫ vertexFiberι p c = vertexFiberι p b := by
  cases h
  exact Category.id_comp _

/-- 引き戻しの fiber 同型の逆も、元の全空間への射影を保持する。 -/
lemma vertexFiberPullbackIso_inv_ι_fst {X B C : SSet.{u}} (p : X ⟶ B) (f : C ⟶ B)
    (c : C _⦋0⦌) :
    (vertexFiberPullbackIso p f c).inv ≫ vertexFiberι (pullback.snd p f) c ≫
      pullback.fst p f = vertexFiberι p (f.app _ c) := by
  rw [← vertexFiberPullbackIso_hom_ι, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
