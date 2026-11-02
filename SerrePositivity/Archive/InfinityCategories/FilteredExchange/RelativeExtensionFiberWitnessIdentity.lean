module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointComposition

/-!
概要：同じ実延長と実 fiber 終点を比較する指定比較は、同じ終点の恒等同型。
方針：元の三比較の合成則に同じ三延長を代入し、同じ同型で消去する。
規約：指定比較を再選択しない。使われ方：二辺を固定した全三角形の長辺比較の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の同じ実延長と同じ実終点の指定比較は、厳密に恒等同型である。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_refl {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W : A ⟶ E) (hp : W ≫ p = a) (hs : i ≫ W = v)
    (g : C ⟶ vertexFiber p b) (hg : j ≫ W = g ≫ vertexFiberι p b) :
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W hp hp hs hs g g hg hg = Iso.refl _ := by
  let e := relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
    W W hp hp hs hs g g hg hg
  have h : e ≪≫ e = e := relativeExtensionFiberEndpoint_witnessIso_trans p a i hi v hv
    j b hj W W W hp hp hp hs hs hs g g g hg hg hg
  have hc := congrArg (fun t => e.symm ≪≫ t) h
  simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using hc

/-- 元の二つの実延長が同じなら、同じ実 fiber 終点の指定比較は厳密に恒等同型。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_eq_refl_of_eq {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hp : W ≫ p = a) (hp' : W' ≫ p = a)
    (hs : i ≫ W = v) (hs' : i ≫ W' = v) (g : C ⟶ vertexFiber p b)
    (hg : j ≫ W = g ≫ vertexFiberι p b) (hg' : j ≫ W' = g ≫ vertexFiberι p b)
    (he : W = W') :
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W' hp hp' hs hs' g g hg hg' = Iso.refl _ := by
  subst W'
  exact relativeExtensionFiberEndpoint_witnessIso_refl p a i hi v hv j b hj W hp hs g hg

end SerrePositivity.InfinityCategories.F2
