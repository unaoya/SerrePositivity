module
public import SerrePositivity.KST.ProExcision.Lemma416

/-!
# 外部作用の単体的モノイド射による制限

概要：外部作用と同変射と実 m 次比較を、別の単体的モノイドの作用へ引き戻す。
方針：次数ごとの作用にモノイド射を前合成し、同変性をその像で評価する。
規約：KST Lemma 4.16 から A.4、Claim 4.15 への適用。
使われ方：群状の ĜL の行列表示に沿って全行列作用を制限する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {G G' H H' : SimplicialObject MonCat.{u}}

/-- 概要：単体的モノイドの射に沿う実作用の制限。
方針：各次数の作用準同型に射を前合成する。
規約：KST 4.16・A.4、群状性はこの構成には不要。
使われ方：行列表示による ĜL の作用。 -/
def SimplicialMonoidAction.restrict (A : SimplicialMonoidAction G H) (ρ : G' ⟶ G) :
    SimplicialMonoidAction G' H where
  action k := (A.action k).comp (ρ.app k).hom
  naturality {k l} φ a b := by
    change (H.map φ).hom (A.action k ((ρ.app k).hom a) b) = _
    rw [A.naturality]
    have hρ := congrArg (fun q ↦ q.hom a) (ρ.naturality φ)
    change (ρ.app l).hom ((G'.map φ).hom a) = (G.map φ).hom ((ρ.app k).hom a) at hρ
    rw [← hρ]
    rfl

/-- 概要：同変射は外部作用の制限後も同変。
方針：元の同変性をモノイド射の像で評価する。
規約：KST A.4。使われ方：実右乗法の作用の制限。 -/
def SimplicialActionHom.restrict {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    (f : SimplicialActionHom A B) (ρ : G' ⟶ G) : SimplicialActionHom (A.restrict ρ) (B.restrict ρ) where
  hom := f.hom
  equivariant k a b := f.equivariant k ((ρ.app k).hom a) b

/-- 概要：実 m 次の同変定数比較は作用の制限で保たれる。
方針：同じ実区間射を使い、各次数の同変性を射の像で評価する。
規約：KST A.3・A.4・4.16。使われ方：ĜL の行列作用への比較の移送。 -/
def HomologicallyMConstant.restrict {A : SimplicialMonoidAction G H} {B : SimplicialMonoidAction G H'}
    {f : SimplicialActionHom A B} {m : ℕ} (h : HomologicallyMConstant f m) (ρ : G' ⟶ G) :
    HomologicallyMConstant (f.restrict ρ) m where
  homotopy := h.homotopy
  equivariant k a := h.equivariant k ((ρ.app k).hom a)

end SerrePositivity.KST.ProExcision
