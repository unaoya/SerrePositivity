module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.AffineCechFrameLift
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# affine 包の係数変更

## 概要
prism の射に沿う affine 包の係数変更を、各頂点の座標を保って作る。

## 方針
包の変数による普遍性を使い、単体の構造射との可換性も同じ一意性で示す。

## 規約
両基底の包の選択と濃度上限を独立に指定する。

## 使われ方
BS 著者版 Proposition 3.13 (2) と Theorem 6.4 の完備底変換の余単体射。
-/

public noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {P' : OrientedPrism p B} (f : OrientedPrism.Hom P P')
variable {r n : ℕ} {κ κ' : Cardinal.{u}}
variable (U : AffineEnvelopeTerm P r n κ) (V : AffineEnvelopeTerm P' r n κ')

private theorem coefficient_existsUnique :
    ∃! g : U.X.B →+* V.X.B,
      U.X.Q.deltaStructure.IsDeltaHom V.X.Q.deltaStructure g ∧
      g.comp U.X.toHom.toRingHom = (V.X.toHom.comp f).toRingHom ∧
      ∀ j i, g (U.η (affineVariable P r n j i)) = V.η (affineVariable P' r n j i) := by
  apply U.existsUnique_liftVariables V.X.Q (V.X.toHom.comp f)
  intro j i
  apply Ideal.Quotient.eq.mpr
  exact affineTerm_difference_mem P' V j i 0

/-- 基底の prism 射に沿って各頂点の座標を保つ環射。 -/
def affineEnvelopeCoefficientMap : U.X.B →+* V.X.B :=
  (coefficient_existsUnique f U V).choose

/-- affine 係数変更の δ 構造、基底脚、頂点での仕様。 -/
theorem affineEnvelopeCoefficientMap_spec :
    U.X.Q.deltaStructure.IsDeltaHom V.X.Q.deltaStructure
        (affineEnvelopeCoefficientMap f U V) ∧
      (affineEnvelopeCoefficientMap f U V).comp U.X.toHom.toRingHom =
        (V.X.toHom.comp f).toRingHom ∧
      ∀ j i, affineEnvelopeCoefficientMap f U V (U.η (affineVariable P r n j i)) =
        V.η (affineVariable P' r n j i) :=
  (coefficient_existsUnique f U V).choose_spec.1

/-- δ 構造、基底と頂点での像が指定された係数変更は一意。 -/
theorem affineEnvelopeCoefficientMap_unique (g : U.X.B →+* V.X.B)
    (hδ : U.X.Q.deltaStructure.IsDeltaHom V.X.Q.deltaStructure g)
    (hb : g.comp U.X.toHom.toRingHom = (V.X.toHom.comp f).toRingHom)
    (hv : ∀ j i, g (U.η (affineVariable P r n j i)) = V.η (affineVariable P' r n j i)) :
    g = affineEnvelopeCoefficientMap f U V :=
  (coefficient_existsUnique f U V).choose_spec.2 g ⟨hδ, hb, hv⟩

variable {m : ℕ} (Um : AffineEnvelopeTerm P r m κ)
variable (Vm : AffineEnvelopeTerm P' r m κ') (θ : ⦋m⦌ ⟶ ⦋n⦌)

/-- affine 係数変更は、任意の単体の構造射と厳密に可換。 -/
theorem affineEnvelopeCoefficientMap_natural :
    (affineEnvelopeCoefficientMap f U V).comp (affineTermMap P Um U θ).toHom.toRingHom =
      (affineTermMap P' Vm V θ).toHom.toRingHom.comp (affineEnvelopeCoefficientMap f Um Vm) := by
  let T := V.X.Q
  let b : OrientedPrism.Hom P T := V.X.toHom.comp f
  let v (j : Fin r) (i : Fin (m + 1)) :=
    V.η (affineVariable P' r n j (θ.toOrderHom i))
  have hv (j : Fin r) (i : Fin (m + 1)) :
      Ideal.Quotient.mk T.ideal (v j i) = Ideal.Quotient.mk T.ideal (v j 0) := by
    apply Ideal.Quotient.eq.mpr
    exact affineTerm_difference_mem P' V j (θ.toOrderHom i) (θ.toOrderHom 0)
  apply (Um.existsUnique_liftVariables T b v hv).unique
  · refine ⟨(affineEnvelopeCoefficientMap_spec f U V).1.comp
        (affineTermMap P Um U θ).toHom.map_delta, ?_, ?_⟩
    · have hbase : (affineTermMap P Um U θ).toHom.toRingHom.comp
          Um.X.toHom.toRingHom = U.X.toHom.toRingHom :=
        congrArg OrientedPrism.Hom.toRingHom (affineTermMap P Um U θ).comm_base
      rw [RingHom.comp_assoc, hbase]
      exact (affineEnvelopeCoefficientMap_spec f U V).2.1
    · intro j i
      change affineEnvelopeCoefficientMap f U V
        ((affineTermMap P Um U θ).toHom.toRingHom (Um.η (affineVariable P r m j i))) = _
      rw [affineTermMap_apply, (affineEnvelopeCoefficientMap_spec f U V).2.2]
  · refine ⟨(affineTermMap P' Vm V θ).toHom.map_delta.comp
        (affineEnvelopeCoefficientMap_spec f Um Vm).1, ?_, ?_⟩
    · rw [RingHom.comp_assoc, (affineEnvelopeCoefficientMap_spec f Um Vm).2.1]
      change (affineTermMap P' Vm V θ).toHom.toRingHom.comp
        (Vm.X.toHom.toRingHom.comp f.toRingHom) = V.X.toHom.toRingHom.comp f.toRingHom
      have hbase : (affineTermMap P' Vm V θ).toHom.toRingHom.comp
          Vm.X.toHom.toRingHom = V.X.toHom.toRingHom :=
        congrArg OrientedPrism.Hom.toRingHom (affineTermMap P' Vm V θ).comm_base
      rw [← RingHom.comp_assoc, hbase]
    · intro j i
      change (affineTermMap P' Vm V θ).toHom.toRingHom
        (affineEnvelopeCoefficientMap f Um Vm (Um.η (affineVariable P r m j i))) = _
      rw [(affineEnvelopeCoefficientMap_spec f Um Vm).2.2, affineTermMap_apply]

end SerrePositivity.BhattScholze.Prismatic
