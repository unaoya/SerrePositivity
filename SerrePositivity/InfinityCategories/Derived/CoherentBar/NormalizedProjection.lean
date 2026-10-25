module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.MaurerCartanMap
/-!
概要：元の実 bar から同じ theta の正規化実 bar への閉零加群射を構成する。
方針：退化列の消滅から得た射影との可換式を MC 加群射の構成に渡す。
規約：元の MC 仮定以外を追加しない。補正包含と鎖ホモトピーは別に構成する。
使われ方：native 余錐と全 Hom 普遍性を正規化側から元の bar へ戻す比較。
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

def dgCoherentBarNormalizedModuleProjection (hMC : dgCoherentBarMaurerCartan R D F) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarModule R D F hMC) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC) :=
  dgCoherentBarMaurerCartanMap R D (dgCoherentBarGraded R D F)
    (dgCoherentBarNormalizedGraded R D F)
    (dgCoherentBarTheta R D F) (dgCoherentBarNormalizedTheta R D F) hMC
    (dgCoherentBarNormalizedTheta_maurerCartan R D F hMC)
    (dgCoherentBarNormalizedProjection R D F) (dgCoherentBarNormalizedTheta_projection R D F)

end SerrePositivity.InfinityCategories
