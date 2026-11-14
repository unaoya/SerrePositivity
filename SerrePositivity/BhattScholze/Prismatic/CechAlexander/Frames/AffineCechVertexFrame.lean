module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.PrismaticFrameHomotopy
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.AffineCechFrameLift
import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechCompletionLift
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.AffinePolynomial
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 有限 affine Čech 枠の頂点の普遍性

## 概要
有限 affine 包を、混合頂点のホモトピーを作れる枠として読む。

## 方針
変数像の普遍性を剰余構造射と照合し、環射を site の射に持ち上げる。

## 使われ方
有限 prismatic 枠上の比較の合成を恒等射に結ぶ。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable {r : ℕ} {κ : Cardinal.{u}} (U : ∀ n, AffineEnvelopeTerm P r n κ)

local notation "R" => prismPolynomialCompletion P (Fin r)
local notation "u" => prismPolynomialUnit P (Fin r)

/-- 有限 affine 枠の各項の普遍性は、剰余構造射を保つ射について成立する。 -/
def affineCechVertexFrame :
    PrismOverVertexFrame P R κ (cechAlexanderOfAffineTerms P U) (Fin r) where
  residue j := u (MvPolynomial.X j)
  variableImage n j i := (U n).η (affineVariable P r n j i)
  variable_mod n j i := by
    change Ideal.Quotient.mk (U n).X.Q.ideal ((U n).η (affineVariable P r n j i)) =
      (U n).X.sec (u (MvPolynomial.X j))
    rw [(U n).sec_X]
    exact Ideal.Quotient.eq.mpr (affineTerm_difference_mem P (U n) j i 0)
  variable_map θ x i := affineTermMap_apply P _ _ θ x i
  lift n Y z hz := by
    let X := U n
    obtain ⟨f, hf, hu⟩ := X.existsUnique_liftVariables Y.Q Y.toHom z
      (fun j i => (hz j i).trans (hz j 0).symm)
    let F : OrientedPrism.Hom X.X.Q Y.Q := ⟨f, hf.1, by
      rw [X.envelope.ideal_eq, Ideal.span_singleton_le_iff_mem]
      change (f.comp (X.η.comp (completedFreeDeltaBase P _))) P.generator ∈ Y.Q.ideal
      rw [X.base_eq, hf.2.1]
      exact Y.toHom.map_generator_mem⟩
    have hbase : F.comp X.X.toHom = Y.toHom := OrientedPrism.Hom.ext hf.2.1
    have hsec : F.quotientMap.comp X.X.sec = Y.sec := by
      have hc := isModuleComplete_principal_quotient_natCast Y.B p Y.Q.generator Y.Q.complete_p
      have h : (F.quotientMap.comp X.X.sec).comp u = Y.sec.comp u := by
        apply MvPolynomial.ringHom_ext'
        · rw [RingHom.comp_assoc, RingHom.comp_assoc]
          change (F.quotientMap.comp X.X.sec).comp (algebraMap (A ⧸ P.ideal) R) =
            Y.sec.comp (algebraMap (A ⧸ P.ideal) R)
          rw [RingHom.comp_assoc, X.X.sec_comp, Y.sec_comp,
            ← OrientedPrism.Hom.quotientMap_comp, hbase]
        · intro j
          simp only [RingHom.comp_apply, X.sec_X, OrientedPrism.Hom.quotientMap_mk]
          rw [show F.toRingHom (X.η (affineVariable P r n j 0)) = z j 0 from hf.2.2 j 0]
          exact hz j 0
      exact (liftFromPolyCompletion_unique p (Y.sec.comp u) hc _ h).trans
        (liftFromPolyCompletion_unique p (Y.sec.comp u) hc Y.sec rfl).symm
    refine ⟨⟨F, hbase, hsec⟩, hf.2.2, ?_⟩
    intro g hg
    apply PrismOver.Hom.ext
    apply OrientedPrism.Hom.ext
    exact hu g.toHom.toRingHom ⟨g.toHom.map_delta,
      congrArg OrientedPrism.Hom.toRingHom g.comm_base, hg⟩

end SerrePositivity.BhattScholze.Prismatic
