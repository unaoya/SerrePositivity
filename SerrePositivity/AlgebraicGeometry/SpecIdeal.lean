module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
概要：KST §5、Stacks 080Y のチャートイデアルに使う Spec 上のイデアル層と環イデアルの対応。
方針：アフィン切断の順序同型を ΓSpec 同型で移し、像と逆像を随伴性から計算する。
規約：既存の IdealSheafData の実際の map・comap を使う。
使われ方：blowup 上のイデアル層から整合するチャートイデアル族を取り出す。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

/--
概要：Spec A 上のイデアル層と A のイデアルの実際の順序同型。
方針：アフィン上の切断の同型と ΓSpec の環同型を合成する。
規約：KST §5、Stacks 080Y、係数環の表示の違いを明示して輸送する。
使われ方：幾何学的なチャートイデアルを元のチャート環に移す。
-/
def specIdealEquiv (A : CommRingCat.{u}) : (Spec A).IdealSheafData ≃o Ideal A :=
  (Scheme.IdealSheafData.equivOfIsAffine (X := Spec A)).toOrderIso.trans
    ((Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.idealComapOrderIso)

/--
概要：Spec のイデアル対応は切断イデアルを ΓSpec の逆射で引き戻す。
方針：順序同型の定義を展開する。
規約：KST §5、Stacks 080Y、全空間のアフィン開集合を使う。
使われ方：イデアルの像の係数計算。
-/
theorem specIdealEquiv_apply (A : CommRingCat.{u}) (K : (Spec A).IdealSheafData) :
    specIdealEquiv A K =
      (K.ideal ⟨⊤, isAffineOpen_top (Spec A)⟩).comap (Scheme.ΓSpecIso A).inv.hom := rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン射によるイデアル層の像は環イデアルの逆像に対応する。
方針：アフィン射の切断イデアル公式と ΓSpec 同型の自然性を使う。
規約：KST §5、Stacks 080Y、任意の環準同型を許す。
使われ方：逆像イデアル層の計算の随伴側。
-/
theorem specIdealEquiv_map {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (K : (Spec B).IdealSheafData) :
    specIdealEquiv A (K.map (Spec.map φ)) = (specIdealEquiv B K).comap φ.hom := by
  rw [specIdealEquiv_apply, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    specIdealEquiv_apply]
  ext r
  change (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv r) ∈
      K.ideal ⟨⊤, isAffineOpen_top (Spec B)⟩ ↔
    (Scheme.ΓSpecIso B).inv (φ r) ∈ K.ideal ⟨⊤, isAffineOpen_top (Spec B)⟩
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィン射によるイデアル層の逆像は環イデアルの拡大に対応する。
方針：像の対応と、イデアル層・環イデアルの二つの Galois 接続から導く。
規約：KST §5、Stacks 080Y、平坦性や開埋め込み性は不要。
使われ方：チャートの重なりで実際のイデアル層の制限を環イデアルの像へ移す。
-/
theorem specIdealEquiv_comap {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (K : (Spec A).IdealSheafData) :
    specIdealEquiv B (K.comap (Spec.map φ)) = (specIdealEquiv A K).map φ.hom := by
  have hL (L : Ideal B) :
      specIdealEquiv B (K.comap (Spec.map φ)) ≤ L ↔ (specIdealEquiv A K).map φ.hom ≤ L := by
    calc
      _ ↔ K.comap (Spec.map φ) ≤ (specIdealEquiv B).symm L := by
        rw [← (specIdealEquiv B).le_iff_le, OrderIso.apply_symm_apply]
      _ ↔ K ≤ ((specIdealEquiv B).symm L).map (Spec.map φ) :=
        Scheme.IdealSheafData.le_map_iff_comap_le.symm
      _ ↔ specIdealEquiv A K ≤
          specIdealEquiv A (((specIdealEquiv B).symm L).map (Spec.map φ)) :=
        (specIdealEquiv A).le_iff_le.symm
      _ ↔ specIdealEquiv A K ≤ L.comap φ.hom := by
        rw [specIdealEquiv_map, OrderIso.apply_symm_apply]
      _ ↔ _ := Ideal.map_le_iff_le_comap.symm
  exact le_antisymm ((hL _).mpr le_rfl) ((hL _).mp le_rfl)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
