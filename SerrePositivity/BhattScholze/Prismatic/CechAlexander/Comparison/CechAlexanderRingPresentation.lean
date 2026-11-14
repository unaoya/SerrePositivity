module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.CechAlexanderPresentation

/-!
# 環の普遍性から site の Čech データへの持ち上げ

## 概要
変数を指定した一意な δ 環射を、site の構造射と両立する一意な射へ移す。

## 方針
prism 射のイデアルの剛性と、変数の剰余の式を使う。

## 規約
BS 著者版 Construction 4.17。一般の包絡と既存 BigCechTerm の共通部品。

## 使われ方
二つの系統で site の射の可換条件の証明を共有する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}} {n : ℕ}

/-- 概要：変数の一意な δ 環射の普遍性から site の項のデータを作る。
方針：prism のイデアルの像の等式でイデアル条件を、各変数の剰余で構造射の可換性を示す。
規約：BS 著者版 Construction 4.17–4.18。
使われ方：一般 HasEnvelopes と既存の大きい枠の組み立てを共通化する。 -/
def ofRingLift (X : PrismOver P R κ) (vX : R × Fin (n + 1) → X.B)
    (hX : ∀ s, Ideal.Quotient.mk X.Q.ideal (vX s) = X.sec s.1)
    (hlift : ∀ (D : PrismOver P R κ) (v : R × Fin (n + 1) → D.B),
      (∀ s, Ideal.Quotient.mk D.Q.ideal (v s) = D.sec s.1) →
      ∃! f : X.B →+* D.B, X.Q.deltaStructure.IsDeltaHom D.Q.deltaStructure f ∧
        f.comp X.toHom.toRingHom = D.toHom.toRingHom ∧ ∀ s, f (vX s) = v s) :
    CechAlexanderPresentation (P := P) (R := R) (κ := κ) n where
  X := X
  coordinate := vX
  coordinate_mod := hX
  liftVariables D v hv := by
    obtain ⟨f, hf, hu⟩ := hlift D v hv
    let F : OrientedPrism.Hom X.Q D.Q := {
      toRingHom := f
      map_delta := hf.1
      ideal_le := by
        rw [← X.toHom.map_ideal_eq, Ideal.map_le_iff_le_comap]
        intro a ha
        change (f.comp X.toHom.toRingHom) a ∈ D.Q.ideal
        rw [hf.2.1]
        exact D.toHom.ideal_le ha }
    have hs : F.quotientMap.comp X.sec = D.sec := by
      apply RingHom.ext
      intro r
      change F.quotientMap (X.sec r) = D.sec r
      rw [← hX (r, 0), OrientedPrism.Hom.quotientMap_mk]
      change Ideal.Quotient.mk D.Q.ideal (f (vX (r, 0))) = _
      rw [hf.2.2]
      exact hv (r, 0)
    let g : X ⟶ D := ⟨F, OrientedPrism.Hom.ext hf.2.1, hs⟩
    refine ⟨g, hf.2.2, ?_⟩
    intro g' hg'
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact hu g'.toHom.toRingHom ⟨g'.toHom.map_delta,
      congrArg OrientedPrism.Hom.toRingHom g'.comm_base, hg'⟩

end SerrePositivity.BhattScholze.Prismatic.CechAlexanderPresentation
