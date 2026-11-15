module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
概要：準コンパクト射によるイデアル層の像と開基底変換の整合性。
方針：閉部分スキームの pullback を貼り、既存の開基底変換の核の公式を使う。
規約：実際の IdealSheafData の等式。
使われ方：Stacks 01PF の有限型部分イデアルの延長の貼り合わせ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 準コンパクト射によるイデアル層の像は開基底変換と整合する。 -/
theorem idealSheaf_comap_map_of_isPullback_openImmersion
    {W X Y S : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Y)
    (j : X ⟶ S) (v : Y ⟶ S) [QuasiCompact j] [IsOpenImmersion v]
    (h : IsPullback a b j v) (K : X.IdealSheafData) :
    (K.map j).comap v = (K.comap a).map b := by
  let t := (K.comapIso a).hom ≫ pullback.snd a K.subschemeι
  have hK : IsPullback (K.comap a).subschemeι t a K.subschemeι := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (K.comapIso a) (by simp) rfl
    dsimp [t]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, K.comapIso_hom_fst]
  have hout := hK.paste_horiz h.flip
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (K.subschemeι ≫ j) ((K.comap a).subschemeι ≫ b) t v hout U).symm

end SerrePositivity.AlgebraicGeometry
