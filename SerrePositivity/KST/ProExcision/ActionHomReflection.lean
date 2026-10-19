module
public import SerrePositivity.KST.ProExcision.ActionMorphisms

/-!
# 実単射同変射による同変性の反映と実同型の逆

概要：実包含との合成から同変性を反映し、実同変な群同型の逆の同変性を示す。
方針：各次数の実単射性と実逆射の法則を用いる。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実 aI の相対包含の因子化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {G H H' H'' : SimplicialObject MonCat.{u}}

/-- 概要：実単射な同変包含との合成から実同変性を反映する。
方針：各次数で実包含の単射性を使い、合成射の同変性を戻す。
規約：KST Proposition 4.14。使われ方：実中心乗法同型の同変性。 -/
def SimplicialActionHom.ofInjectiveComposite
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    {C : SimplicialMonoidAction G H''} (f : H ⟶ H') (j : SimplicialActionHom B C)
    (hj : ∀ k, Function.Injective (j.hom.app k).hom) (g : SimplicialActionHom A C)
    (he : f ≫ j.hom = g.hom) : SimplicialActionHom A B where
  hom := f
  equivariant k a v := by
    apply hj k
    have h (x : H.obj k) : (j.hom.app k).hom ((f.app k).hom x) = (g.hom.app k).hom x :=
      congrArg (fun t : H ⟶ H'' ↦ (t.app k).hom x) he
    calc
      (j.hom.app k).hom ((f.app k).hom (A.action k a v)) =
          (g.hom.app k).hom (A.action k a v) := h _
      _ = C.action k a ((g.hom.app k).hom v) := g.equivariant k a v
      _ = C.action k a ((j.hom.app k).hom ((f.app k).hom v)) := congrArg (C.action k a) (h v).symm
      _ = (j.hom.app k).hom (B.action k a ((f.app k).hom v)) := (j.equivariant k a _).symm

/-- 概要：実同変な単体的モノイド同型の逆も実同変。
方針：各次数の実同型の単射性を使い、正方向の実同変性と実逆射を合成する。
規約：KST Proposition 4.14。使われ方：実 aI のファイバー同型の逆。 -/
def SimplicialActionHom.inverseOfIso
    {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    (e : H ≅ H') (he : ∀ k (a : G.obj k) (v : H.obj k),
      (e.hom.app k).hom (A.action k a v) = B.action k a ((e.hom.app k).hom v)) :
    SimplicialActionHom B A where
  hom := e.inv
  equivariant k a v := by
    apply (e.app k).monCatIsoToMulEquiv.injective
    change (e.hom.app k).hom ((e.inv.app k).hom (B.action k a v)) =
      (e.hom.app k).hom (A.action k a ((e.inv.app k).hom v))
    rw [he]
    have h (x : H'.obj k) : (e.hom.app k).hom ((e.inv.app k).hom x) = x :=
      congrArg (fun t : H' ⟶ H' ↦ (t.app k).hom x) e.inv_hom_id
    rw [h, h]

end SerrePositivity.KST.ProExcision
