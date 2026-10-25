module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateInvariant
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.MaurerCartanDescent
/-!
概要：元の theta を非退化因子へ降ろし、同じ MC 仮定から実正規化 dg 加群を作る。
方針：全退化列の消滅で正規化射影との可換式を得て、分裂射影の MC 降下を適用する。
規約：D の元の MC 方程式だけを入力にする。変形 retract の存在は別に証明する。
使われ方：正規化側の native 余錐と、元の bar への鎖ホモトピー比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarNormalizedTheta :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).X 1 :=
  (eHomWhiskerRight (Complex R) (dgCoherentBarNormalizedInclusion R D F)
    (dgCoherentBarNormalizedGraded R D F)).f 1
    ((eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f 1 (dgCoherentBarTheta R D F))

lemma dgCoherentBarNormalizedTheta_projection :
    (eHomWhiskerRight (Complex R) (dgCoherentBarNormalizedProjection R D F)
      (dgCoherentBarNormalizedGraded R D F)).f 1 (dgCoherentBarNormalizedTheta R D F) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f 1 (dgCoherentBarTheta R D F) := by
  apply dgCoherentBarHom_factor_normalized R D F (dgCoherentBarNormalizedGraded R D F) 1
  intro s
  have h := congrArg (fun f => f.f 1 (dgCoherentBarTheta R D F))
    (eHom_whisker_exchange (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s.val)
      (dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s.val)
      (dgCoherentBarNormalizedGraded R D F)).f 1
      ((eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
        (dgCoherentBarNormalizedProjection R D F)).f 1 (dgCoherentBarTheta R D F)) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s.val)
      (dgCoherentBarNormalizedProjection R D F)).f 1
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s.val)
        (dgCoherentBarGraded R D F)).f 1 (dgCoherentBarTheta R D F)) at h
  rw [h, dgCoherentBarTheta_restrict]
  exact dgCoherentBarColumn_degenerate_normalizedProjection R D F s

lemma dgCoherentBarNormalizedTheta_maurerCartan (hMC : dgCoherentBarMaurerCartan R D F) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))).d 1 2
        (dgCoherentBarNormalizedTheta R D F) +
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
      (dgCoherentBarNormalizedTheta R D F) (dgCoherentBarNormalizedTheta R D F)
      (show (1 : ℤ) + 1 = 2 from rfl) = 0 :=
  dgCoherentBar_maurerCartan_of_split_projection R D
    (dgCoherentBarNormalizedInclusion R D F) (dgCoherentBarNormalizedProjection R D F)
    (dgCoherentBarNormalizedInclusion_projection R D F) (dgCoherentBarTheta R D F)
    (dgCoherentBarNormalizedTheta R D F) (dgCoherentBarNormalizedTheta_projection R D F) hMC

def dgCoherentBarNormalizedModule (hMC : dgCoherentBarMaurerCartan R D F) : RightModule R D :=
  moduleMaurerCartan R D (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D F))
    (dgCoherentBarNormalizedTheta R D F) (dgCoherentBarNormalizedTheta_maurerCartan R D F hMC)

end SerrePositivity.InfinityCategories
