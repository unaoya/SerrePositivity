module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# 二座標の分冪完備化の比較

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v

/-! ## 正則主剰余から二元完全平坦性を戻す

## 概要

d が基底環と係数加群で正則なら、mod d の a 完全平坦性から元の (a,d) 完全平坦性が従う。
BS 著者版 Remark 7.15（著者版 p.62）の実候補の導来剰余を δ 完全化へ渡す一般計算。

## 方針

正則性で mod d の高次 Tor を消し、d で消える試験加群の Tor を底変換後に計算する。

## 規約

完備性・Noether 性・通常平坦性は要求しない。

## 使われ方

H/d の p 完全平坦性を実完備化 H の (p,d) 完全平坦性へ戻す。
-/

@[expose] public noncomputable section PDCompletionCoordinateEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {A B : Type u} [CommRing A] [CommRing B] (p : ℕ)

/-- 概要：座標を保つ環射は実完備化 H⁰ 間の環射へ一意に延長する。
方針：標的自身の p,d' 導来完備性を実 H⁰ の環普遍性へ渡す。
規約：係数射の合成を固定し、d の正則性は要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化比較の構成。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準完備化比較射。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用の保存。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 同型の実完備化への延長。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余係数の追跡。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw δ 比較の延長。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の Frobenius 比較の実完備化への移送。 -/
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

end PDCompletionCoordinateEquiv

/-! ## 両座標を殺す商と実導来完備化 H⁰

## 概要

p,d を含むイデアル I に対し、実導来 (p,d) 完備化 H⁰ の I の像による商は A/I と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の完備化後の剰余を具体的な未完備の剰余へ戻す比較。

## 方針

商では p,d が零なので、標準商射を実 H⁰ の環普遍性で延長する。
係数からの逆射を作り、逆合成を商の普遍性と実完備化の一意性で確認する。

## 規約

実際の H⁰ と標準単位を用いる。p,d の正則性・Noether 性を仮定しない。

## 使われ方

Frobenius 側の実完備化の (p,d) 商を、raw 包の同じ剰余へ同定する。
-/

