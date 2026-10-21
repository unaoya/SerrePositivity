module

public import SerrePositivity.InfinityCategories.F1.FiberTransportSquare
public import SerrePositivity.InfinityCategories.F1.PullbackTransport
public import SerrePositivity.InfinityCategories.F1.LeftFibrationTransportNaturality

/-!
概要：底も動く left fibration の正方形で、輸送の同値性を検出する。
方針：正方形を元の pullback に因子化し、同じ底での自然性と pullback 輸送を使う。
規約：元の正方形と元の辺を保持し、底の充填性は仮定しない。
使われ方：空間値錐の底制限と頂点評価により、同じ比較辺の可逆性を検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の正方形の fiber 射は、元の pullback への射と元の fiber 同型の合成。 -/
lemma transportSquareFiberMap_factor {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    (b : B _⦋0⦌) :
    vertexFiberMap p (pullback.snd q g) (pullback.lift f p h)
        (pullback.lift_snd f p h) b ≫ (vertexFiberPullbackIso q g b).hom =
      transportSquareFiberMap p q f g h b := by
  apply vertexFiber_hom_ext q (g.app _ b)
  rw [Category.assoc, vertexFiberPullbackIso_hom_ι, ← Category.assoc, vertexFiberMap_ι,
    Category.assoc, pullback.lift_fst]
  rfl

/-- 両端 fiber の元の正方形が同値なら、元の辺の輸送と像の辺の輸送の同値性は一致する。 -/
lemma transportSquare_isQCatEquivalence_iff {E B F D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (g : B ⟶ D) (h : f ≫ q = p ≫ g)
    {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (ha : IsQCatEquivalence (transportSquareFiberMap p q f g h a))
    (hb : IsQCatEquivalence (transportSquareFiberMap p q f g h b)) :
    IsQCatEquivalence (edgeTransport p e) ↔
      IsQCatEquivalence (edgeTransport q (e.map g)) := by
  have hfa := (qCatEquivalenceOfIso (vertexFiberPullbackIso q g a)).isQCatEquivalence
  have hfb := (qCatEquivalenceOfIso (vertexFiberPullbackIso q g b)).isQCatEquivalence
  have ha' := hfa.cancel_right ((transportSquareFiberMap_factor p q f g h a).symm ▸ ha)
  have hb' := hfb.cancel_right ((transportSquareFiberMap_factor p q f g h b).symm ▸ hb)
  exact (leftFibrationMap_transport_isQCatEquivalence_iff p (pullback.snd q g)
    (pullback.lift f p h) (pullback.lift_snd f p h) e ha' hb').trans
      (edgeTransport_pullback_isQCatEquivalence_iff q g e)

end SerrePositivity.InfinityCategories.HomotopyLimits
