module
public import SerrePositivity.KST.ProExcision.MonoidBarReverseOpposite
public import SerrePositivity.KST.ProExcision.HomologyReversal
public import SerrePositivity.KST.ProExcision.HatGLReverseOppositeIso

/-!
# 反対転置の実 bar 同型と借用する H_* への移送

概要：二方向の実反転同型を、実符号付き鎖同型を介して既存 H_* に移す。
方針：空間の実同型と既存の自然な複体模型の同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。反転不変性を新しい入力にしない。
使われ方：行側相対零化の比較の基底部分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open Comparison

/-- 概要：単体的モノイドの実同型から対角 bar の実同型を作る。
方針：実写像の合成・恒等射保存と元の実逆射を用いる。
規約：KST App. A。使われ方：非可換な反対転置の bar への適用。 -/
def monoidBarIso {M N : SimplicialObject MonCat.{u}} (e : M ≅ N) :
    monoidBar M ≅ monoidBar N where
  hom := monoidBarMap e.hom
  inv := monoidBarMap e.inv
  hom_inv_id := by rw [← monoidBarMap_comp, e.hom_inv_id, monoidBarMap_id]
  inv_hom_id := by rw [← monoidBarMap_comp, e.inv_hom_id, monoidBarMap_id]

/-- 概要：反転した反対モノイドの実 bar ホモロジー同型。
方針：対角 bar の実同型と実鎖反転から得た H_* の同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。H_* の模型だけを明示的に借用する。
使われ方：実比較による行側への移送。 -/
def monoidBarReverseOppositeHomologyIso (M : SimplicialObject MonCat.{u})
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    F.obj (monoidBar (monoidReverseOpposite M)) ≅ F.obj (monoidBar M) :=
  F.mapIso (monoidBarReverseOppositeIso M) ≪≫ hF.reversalNatIso.app (monoidBar M)

/-- 概要：非単位環の反対転置による実 ĜL bar 同型。
方針：実単体的乗法同型の bar と対角全体の反転の同型を合成する。
規約：KST Proposition 4.14、非可換な行側比較。使われ方：基底の実空間比較。 -/
def NonUnitalSimplicialRing.reverseOppositeHatGLBarIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    monoidBar (I.reverseOpposite.hatGL n) ≅ (monoidBar (I.hatGL n)).op :=
  monoidBarIso (I.reverseOppositeHatGLIso n) ≪≫ monoidBarReverseOppositeIso (I.hatGL n)

/-- 概要：非単位環の反対転置による実 ĜL ホモロジー同型。
方針：実 ĜL bar 同型を H_* に写し、実鎖反転の同型を合成する。
規約：KST Proposition 4.14、SW92 §1.2。可換性も次数ごとの可逆性も追加しない。
使われ方：行側半直積の基底の比較。 -/
def NonUnitalSimplicialRing.reverseOppositeHatGLHomologyIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    F.obj (monoidBar (I.reverseOpposite.hatGL n)) ≅ F.obj (monoidBar (I.hatGL n)) :=
  F.mapIso (I.reverseOppositeHatGLBarIso n) ≪≫
    hF.reversalNatIso.app (monoidBar (I.hatGL n))

end SerrePositivity.KST.ProExcision
