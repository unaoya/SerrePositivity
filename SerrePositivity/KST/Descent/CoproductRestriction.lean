module

public import SerrePositivity.KST.Descent.FiniteCoproduct

/-!
# 有限非交和と開制限の標準比較

## 概要
有限個の射を非交和にまとめてから開集合へ制限したスキームと、
各射の制限の非交和との標準同型を構成する。

## 方針
スキームの有限非交和の普遍性が底変換で保たれる Mathlib の定理を使う。
二つの実際の引き戻し正方形を比較し、指定された射との可換式を保持する。

## 規約
台の同相だけでなく、スキームの同型と射の等式を構成する。
前層 L の降下はこの幾何的な比較には使わない。

## 使われ方
論文 定理 3.1 の制限切断の非交和の同型を、軌道射自体の制限の同型へ移す。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {I : Type u} [Finite I] {Y : I → Scheme.{u}} {X : Scheme.{u}}

/-- 概要：各成分の開制限の非交和は元の非交和射の引き戻し（論文 定理 3.1）。
方針：有限非交和の universal colimit 性を、各成分の実際の制限正方形へ適用する。
規約：四辺はスキームの射であり、点集合の Cartesian 性ではない。
使われ方：非交和と開制限の標準比較の構成。 -/
theorem coproductRestriction_isPullback (f : ∀ i, Y i ⟶ X) (U : X.Opens) :
    IsPullback (Sigma.desc fun i ↦ f i ∣_ U)
      (Sigma.desc fun i ↦ (f i ⁻¹ᵁ U).ι ≫ Sigma.ι Y i) U.ι (Sigma.desc f) := by
  have universal : IsUniversalColimit (Cofan.mk (∐ Y) (Sigma.ι Y)) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  convert!
    universal.isPullback_of_isColimit_left f (Sigma.desc f) U.ι
      (fun i ↦ f i ∣_ U) (fun i ↦ (f i ⁻¹ᵁ U).ι)
      (fun i ↦ isPullback_morphismRestrict (f i) U)
      (coproductIsCoproduct (fun i ↦ (f i ⁻¹ᵁ U).toScheme))
      (fun i ↦ Sigma.ι_comp_desc _ _) using 1

/-- 概要：有限非交和と開制限の標準同型（論文 定理 3.1）。
方針：各制限の非交和と実際の全体の制限を、同じ引き戻しの二つの表示として比較する。
規約：始域は各射の開逆像の非交和。
使われ方：制限した切断の同型から軌道射の制限の同型を得る。 -/
noncomputable def coproductRestrictionIso (f : ∀ i, Y i ⟶ X) (U : X.Opens) :
    (∐ fun i ↦ (f i ⁻¹ᵁ U).toScheme) ≅ (Sigma.desc f ⁻¹ᵁ U).toScheme :=
  (coproductRestriction_isPullback f U).isoIsPullback _ _
    (isPullback_morphismRestrict (Sigma.desc f) U)

/-- 概要：標準比較は終域の開集合への指定射と可換（論文 定理 3.1）。
方針：引き戻しの比較同型の第一射影の式を使う。
規約：各射の制限の非交和そのものとの可換式。
使われ方：軌道射の開制限の同型性の移行。 -/
@[reassoc (attr := simp)] theorem coproductRestrictionIso_hom_restriction
    (f : ∀ i, Y i ⟶ X) (U : X.Opens) :
    (coproductRestrictionIso f U).hom ≫ (Sigma.desc f ∣_ U) =
      Sigma.desc (fun i ↦ f i ∣_ U) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- 概要：各制限の非交和の同型性は元の非交和射の開制限に移る（定理 3.1）。
方針：標準比較の可換式と、同型との合成の消去を使う。
規約：指定射の同型性を主張する。
使われ方：抽象 blowup の補集合上の同型条件。 -/
theorem coproductRestriction_isIso (f : ∀ i, Y i ⟶ X) (U : X.Opens)
    [IsIso (Sigma.desc fun i ↦ f i ∣_ U)] : IsIso (Sigma.desc f ∣_ U) := by
  have : IsIso ((coproductRestrictionIso f U).hom ≫ (Sigma.desc f ∣_ U)) := by
    rw [coproductRestrictionIso_hom_restriction]
    infer_instance
  exact IsIso.of_isIso_comp_left (coproductRestrictionIso f U).hom _

end SerrePositivity.KST.Descent
