module

public import SerrePositivity.InfinityCategories.Kan.Pointed.InternalHomTensor

/-!
概要：内部 Hom の二つの源の交換同型の標的に関する自然性。
方針：反復 curry の自然同型と braiding の前合成の自然同型を合成する。
規約：通常の閉 braided モノイダル圏の主張。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop 値のホモトピー類の標的の自然性。
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

/-- 概要：内部 Hom の源の交換を標的についての自然同型としてまとめる。
方針：反復 curry、braiding の前合成、反復 curry の逆を合成する。
規約：標的を動かす二つの反復内部 Hom 関手の同型。
使われ方：HA §1.4.2。二重 loop の標的の変換との可換性。 -/
def naturalIso (A K : C) : ihom K ⋙ ihom A ≅ ihom A ⋙ ihom K :=
  (InternalHomTensor.natIso K A).symm ≪≫
    NatIso.ofComponents (fun Y => preIso (β_ A K) Y)
      (fun f => (MonoidalClosed.pre (β_ A K).hom).naturality f) ≪≫
    InternalHomTensor.natIso A K

/-- 概要：自然同型の各成分は既存の源の交換同型に一致。
方針：反復 curry の同型の Mathlib の定義との一致を使う。
規約：既存の交換の射を変更しない。
使われ方：Goerss–Jardine I §7。成分の具体的な計算と標的の自然性の接続。 -/
@[simp]
theorem naturalIso_app (A K Y : C) : (naturalIso A K).app Y = iso A K Y := by
  apply Iso.ext
  change (InternalHomTensor.iso K A Y).inv ≫ (preIso (β_ A K) Y).hom ≫
    (InternalHomTensor.iso A K Y).hom = _
  rw [InternalHomTensor.iso_eq_ihomCurryIso, InternalHomTensor.iso_eq_ihomCurryIso]
  rfl

/-- 概要：内部 Hom の交換は標的の写像の二重の後合成と可換。
方針：源の交換の自然同型の自然性を取り出す。
規約：標的の写像は任意。
使われ方：Goerss–Jardine I §7、HA §1.4.2。基本群と loop 値の類の標的の自然性。 -/
@[reassoc]
theorem natural_post (A K : C) {Y Z : C} (f : Y ⟶ Z) :
    (ihom A).map ((ihom K).map f) ≫ (iso A K Z).hom =
      (iso A K Y).hom ≫ (ihom K).map ((ihom A).map f) := by
  have h := (naturalIso A K).hom.naturality f
  change (ihom A).map ((ihom K).map f) ≫ ((naturalIso A K).app Z).hom =
    ((naturalIso A K).app Y).hom ≫ (ihom K).map ((ihom A).map f) at h
  simpa only [naturalIso_app] using h

end

end SerrePositivity.KST.Spectra.InternalHomExchange
