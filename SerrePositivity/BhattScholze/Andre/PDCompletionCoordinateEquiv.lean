module

public import SerrePositivity.BhattScholze.DeltaPDCompletionUniversal

/-!
# André E1・E2：座標を保つ環同型による実導来完備化の比較

## 概要

環射が d を d' に送れば、実導来 (p,d) 完備化の H⁰ から (p,d') 完備化の H⁰ へ
標準係数射を保つ一意な環射がある。元の射が環同型なら延長も環同型。
BS Rem 7.15（著者版 p.62）の raw 比較を完備化へ通すための一般計算。

## 方針

既存の実導来完備性と H⁰ の環としての普遍性を使う。
逆合成は標準単位との合成で一致することから一意性で確認する。

## 規約

実際の PDCompletionH0 と既存の環構造・単位を使い、正則性を追加しない。

## 使われ方

raw δ 包の係数自己同型による比較を、指定生成元の完備化の比較へ延長する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A B : Type u} [CommRing A] [CommRing B] (p : ℕ)

/-- 概要：座標を保つ環射は実完備化 H⁰ 間の環射へ一意に延長する。
方針：標的自身の p,d' 導来完備性を実 H⁰ の環普遍性へ渡す。
規約：係数射の合成を固定し、d の正則性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の完備化比較の構成。 -/
theorem existsUnique_pdCompletionCoordinateMap (g : A →+* B) (d : A) (d' : B)
    (hd : g d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    ∃! F : PDCompletionH0 A p d →+* PDCompletionH0 B p d',
      F.comp (pdCompletionUnit A p d) = (pdCompletionUnit B p d').comp g := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  apply existsUnique_pdCompletionRingHom A p d (PDCompletionH0 B p d')
    ((pdCompletionUnit B p d').comp g) (pdCompletionH0_self_complete_p B p d')
  simpa only [RingHom.comp_apply, hd] using pdCompletionH0_self_complete_d B p d'

/-- 概要：指定座標を保つ環射から実完備化間の標準環射を選ぶ。
方針：一意延長の存在から選択する。
規約：既存の実 H⁰ の環構造を局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の標準完備化比較射。 -/
def pdCompletionCoordinateMap (g : A →+* B) (d : A) (d' : B) (hd : g d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    PDCompletionH0 A p d →+* PDCompletionH0 B p d' := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  exact (existsUnique_pdCompletionCoordinateMap p g d d' hd).choose

/-- 概要：完備化間の標準射は元の標準係数射と可換。
方針：選んだ一意延長の仕様を使う。
規約：環射の合成の等式として述べる。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用の保存。 -/
theorem pdCompletionCoordinateMap_comp_unit
    (g : A →+* B) (d : A) (d' : B) (hd : g d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    (pdCompletionCoordinateMap p g d d' hd).comp (pdCompletionUnit A p d) =
      (pdCompletionUnit B p d').comp g := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  exact (existsUnique_pdCompletionCoordinateMap p g d d' hd).choose_spec.1

/-- 概要：座標を保つ環同型は実導来完備化 H⁰ の環同型を誘導する。
方針：順逆の一意延長を作り、逆合成を標準単位上の一意性で検証する。
規約：古典的完備化や Noether 性に置き換えない。
使われ方：BS Rem 7.15（著者版 p.62）の raw 同型の実完備化への延長。 -/
def pdCompletionCoordinateEquiv (e : A ≃+* B) (d : A) (d' : B) (hd : e d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    PDCompletionH0 A p d ≃+* PDCompletionH0 B p d' := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  have hi : e.symm d' = d := by rw [← hd, RingEquiv.symm_apply_apply]
  let F := pdCompletionCoordinateMap p e.toRingHom d d' hd
  let G := pdCompletionCoordinateMap p e.symm.toRingHom d' d hi
  have hF := pdCompletionCoordinateMap_comp_unit p e.toRingHom d d' hd
  have hG := pdCompletionCoordinateMap_comp_unit p e.symm.toRingHom d' d hi
  apply RingEquiv.ofRingHom F G
  · apply pdCompletionRingHom_ext B p d' (PDCompletionH0 B p d') (pdCompletionUnit B p d')
      (pdCompletionH0_self_complete_p B p d') (pdCompletionH0_self_complete_d B p d')
    · change (F.comp G).comp (pdCompletionUnit B p d') = pdCompletionUnit B p d'
      rw [RingHom.comp_assoc, hG, ← RingHom.comp_assoc, hF]
      ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
    · exact RingHom.id_comp _
  · apply pdCompletionRingHom_ext A p d (PDCompletionH0 A p d) (pdCompletionUnit A p d)
      (pdCompletionH0_self_complete_p A p d) (pdCompletionH0_self_complete_d A p d)
    · change (G.comp F).comp (pdCompletionUnit A p d) = pdCompletionUnit A p d
      rw [RingHom.comp_assoc, hF, ← RingHom.comp_assoc, hG]
      ext b
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    · exact RingHom.id_comp _

/-- 概要：完備化比較同型は任意の元の標準完備化像を対応させる。
方針：順射の標準単位との可換性を各元で評価する。
規約：座標元だけでなく全ての係数元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の完備化後の剰余係数の追跡。 -/
theorem pdCompletionCoordinateEquiv_unit
    (e : A ≃+* B) (d : A) (d' : B) (hd : e d = d') (b : A) :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    pdCompletionCoordinateEquiv p e d d' hd (pdCompletionUnit A p d b) =
      pdCompletionUnit B p d' (e b) := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  exact RingHom.congr_fun (pdCompletionCoordinateMap_comp_unit p e.toRingHom d d' hd) b

variable [Fact p.Prime]

/-- 概要：座標を保つ δ 射の標準完備化延長は実 δ 射。
方針：既存の実完備化の δ 普遍性に元の δ 射と座標の等式を供給する。
規約：両側で既存の deltaPDCompletionStructure を使う。
使われ方：BS Rem 7.15（著者版 p.62）の raw δ 比較の延長。 -/
theorem pdCompletionCoordinateMap_isDeltaHom
    (D : DeltaStructure p A) (E : DeltaStructure p B) (g : A →+* B)
    (hg : D.IsDeltaHom E g) (d : A) (d' : B) (hd : g d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    (deltaPDCompletionStructure D d).IsDeltaHom (deltaPDCompletionStructure E d')
      (pdCompletionCoordinateMap p g d d' hd) := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  have hcomplete : IsModuleComplete (PDCompletionH0 B p d')
      (((pdCompletionUnit B p d').comp g) d)
      (ModuleCat.of (PDCompletionH0 B p d') (PDCompletionH0 B p d')) := by
    simpa only [RingHom.comp_apply, hd] using pdCompletionH0_self_complete_d B p d'
  exact pdCompletionRingHom_isDeltaHom D d (deltaPDCompletionStructure E d')
    ((pdCompletionUnit B p d').comp g) ((pdCompletionUnit_isDeltaHom E d').comp hg)
    (pdCompletionH0_self_complete_p B p d') hcomplete
    (pdCompletionCoordinateMap p g d d' hd) (pdCompletionCoordinateMap_comp_unit p g d d' hd)

/-- 概要：座標を保つ δ 環同型の標準完備化同型は実 δ 射。
方針：順射が標準完備化延長であることとその δ 互換性を使う。
規約：環同型と座標の等式以外の正則性仮定を置かない。
使われ方：BS Rem 7.15（著者版 p.62）の Frobenius 比較の実完備化への移送。 -/
theorem pdCompletionCoordinateEquiv_isDeltaHom
    (D : DeltaStructure p A) (E : DeltaStructure p B) (e : A ≃+* B)
    (he : D.IsDeltaHom E e.toRingHom) (d : A) (d' : B) (hd : e d = d') :
    letI := pdCompletionCommRing A p d
    letI := pdCompletionCommRing B p d'
    (deltaPDCompletionStructure D d).IsDeltaHom (deltaPDCompletionStructure E d')
      (pdCompletionCoordinateEquiv p e d d' hd).toRingHom := by
  let := pdCompletionCommRing A p d
  let := pdCompletionCommRing B p d'
  exact pdCompletionCoordinateMap_isDeltaHom p D E e.toRingHom he d d' hd

end SerrePositivity.BhattScholze.Andre
