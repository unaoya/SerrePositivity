module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.ActionDescent

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# 群状作用の半直積上の台写像の可逆性

概要：KST Lemma A.2 の ψ(g,h)=(g,g(h)) を anodyne 局所化で可逆にする。
方針：半直積の台を直積と同定し、一般の族による作用のセル降下を適用する。
規約：原典の fibration とファイバー比較とは異なる、セル濾過による証明経路。
使われ方：Prop A.1 の二重 bar 比較の各行の同値性。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.KST.Comparison SerrePositivity.SimplicialModel
variable {G H : SimplicialObject MonCat.{u}}

/-- 概要：単体的半直積の台単体集合は二つの台の直積。
方針：二つの成分を取り出す写像と構造体へ戻す写像を使う。
規約：モノイドの積の同型とは主張しない。
使われ方：KST Lemma A.2 の ψ と族の作用の比較。 -/
def simplicialActionProductUnderlyingIso (A : SimplicialMonoidAction G H) :
    monoidSpace (simplicialActionProduct A) ≅ monoidSpace G ⊗ monoidSpace H where
  hom :=
    { app n := TypeCat.ofHom (fun x ↦ (x.base, x.fiber))
      naturality _ _ _ := by rfl }
  inv :=
    { app n := TypeCat.ofHom (fun p ↦ ⟨p.1, p.2⟩)
      naturality _ _ _ := by rfl }
  hom_inv_id := by rfl
  inv_hom_id := by rfl

/-- 概要：半直積の ψ は恒等パラメータによる作用の族へ移る。
方針：半直積の台の二つの座標を評価する。
規約：台単体集合の写像の等式。
使われ方：KST Lemma A.2 の全体での局所化可逆性。 -/
theorem simplicialActionProductTwist_underlying (A : SimplicialMonoidAction G H) :
    simplicialActionProductTwist A ≫ (simplicialActionProductUnderlyingIso A).hom =
      (simplicialActionProductUnderlyingIso A).hom ≫ actionFamily A (𝟙 (monoidSpace G)) := by
  rfl

/-- 概要：群状単体モノイドによる半直積の ψ は anodyne 局所化で同型。
方針：直積上の作用の族の可逆性を、台単体集合の標準同型で移す。
規約：KST Lemma A.2。原典と異なり標準単体の収縮とセルの貼り合わせを使う。
使われ方：Prop A.1 の bar 比較の各行。π による同値性への移送は K-L9 の模型界面。 -/
theorem simplicialActionProductTwist_localized_isIso (A : SimplicialMonoidAction G H)
    (hG : SimplicialMonoid.IsGrouplike G) :
    IsIso (AnodyneHomotopy.anodyneQ.map (simplicialActionProductTwist A)) := by
  have hi : IsIso (AnodyneHomotopy.anodyneQ.map (actionFamily A (𝟙 (monoidSpace G)))) :=
    actionFamily_localized_isIso A hG _
  have h := congrArg AnodyneHomotopy.anodyneQ.map (simplicialActionProductTwist_underlying A)
  simp only [Functor.map_comp] at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map (simplicialActionProductTwist A) ≫
      AnodyneHomotopy.anodyneQ.map (simplicialActionProductUnderlyingIso A).hom) :=
    h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma A.2" (partial := component) "仮定：群状単体モノイドの作用を持つ（原典と一致）。結論：ねじり (g,h)↦(g,g(h)) が anodyne 局所化で同型。Kan 模型を経た原典の弱同値との比較は別（Lean が弱い）。"] _root_.SerrePositivity.KST.ProExcision.simplicialActionProductTwist_localized_isIso
