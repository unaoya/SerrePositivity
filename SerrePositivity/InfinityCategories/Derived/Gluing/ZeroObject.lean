module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ZeroRepresentation

/-! 零加群の表現可能性から、K(Gluing) で零を表す実 gluing 対象を選ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "G" => DGGluingObject R C D M
local notation "K" => moduleToHomotopy R (DGGluingObject R C D M)

/-- 同じ零加群と代表加群との、全 dg 自然な K(Gluing) 同型の存在。 -/
lemma dgGluingZeroRepresentative_exists
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    ∃ X : G, Nonempty ((K).obj (moduleZero R G) ≅
      (K).obj (ForgetEnrichment.of (Complex R) (representable R X))) := by
  have hz := dgGluingZeroHomotopyRepresentable R C D M hC hD
  change dgRepresentableHomotopyProperty R G ((K).obj (moduleZero R G)) at hz
  exact (dgRepresentableHomotopyProperty_iff R G _).1 hz

/-- 元の両圏の前三角性を明示入力に選ぶ、零を表す実 gluing 対象。 -/
def dgGluingZeroObject (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) : G :=
  Classical.choose (dgGluingZeroRepresentative_exists R C D M hC hD)

/-- 選んだ同じ零対象の代表加群と零加群との K(Gluing) 同型。 -/
def dgGluingZeroRepresentableIso
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    (K).obj (moduleZero R G) ≅ (K).obj
      (ForgetEnrichment.of (Complex R) (representable R (dgGluingZeroObject R C D M hC hD))) :=
  Classical.choice (Classical.choose_spec (dgGluingZeroRepresentative_exists R C D M hC hD))

/-- 選んだ実零対象の代表加群は K(Gluing) で零。 -/
lemma dgGluingZeroObject_isZero_homotopy
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    IsZero ((K).obj (ForgetEnrichment.of (Complex R)
      (representable R (dgGluingZeroObject R C D M hC hD)))) :=
  ((K).map_isZero (moduleZero_isZero R G)).of_iso
    (dgGluingZeroRepresentableIso R C D M hC hD).symm

end SerrePositivity.InfinityCategories
