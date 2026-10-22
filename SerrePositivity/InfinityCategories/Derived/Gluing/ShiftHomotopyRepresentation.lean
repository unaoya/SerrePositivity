module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ShiftModuleQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations

/-! 同じ全 dg 自然なシフト比較を K(Gluing) の同型へ送り、全整数シフトを表現する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M) (n : ℤ)
  (p : DGGluingShiftRepresentative R C X.left n)
  (q : DGGluingShiftRepresentative R D X.right n)
local notation "G" => DGGluingObject R C D M
local notation "W" => dgGluingShiftObjectFromRepresentatives R C D M X n p q
local notation "K" => moduleToHomotopy R G

/-- 同じシフト比較は、射影的加群間の quasi-isomorphism なので K で同型。 -/
lemma dgGluingShiftModuleMap_isIso_homotopy :
    IsIso ((K).map (dgGluingShiftModuleMap R C D M X n p q)) :=
  moduleHomotopicallyProjective_quasiIso_isIso_homotopy R G
    (moduleHomotopicallyProjective_shift R G (representable_homotopicallyProjective R G X) n)
    (representable_homotopicallyProjective R G W)
    (dgGluingShiftModuleMap R C D M X n p q)
    (dgGluingShiftModuleMap_quasiIso R C D M X n p q)

/-- 指定した同じ実加群比較を順射に保持する、全整数シフトの K 同型。 -/
def dgGluingShiftModuleHomotopyIso :
    (K).obj (ForgetEnrichment.of (Complex R) (shiftModule n (representable R X))) ≅
      (K).obj (ForgetEnrichment.of (Complex R) (representable R W)) := by
  letI := dgGluingShiftModuleMap_isIso_homotopy R C D M X n p q
  exact asIso ((K).map (dgGluingShiftModuleMap R C D M X n p q))

include p q in
/-- 同じ Yoneda 加群の全整数シフトは、全 dg 自然な加群のホモトピー圏で表現可能。 -/
lemma dgGluingShiftHomotopyRepresentable :
    dgHomotopyRepresentable R G (shiftModule n (representable R X)) :=
  (dgRepresentableHomotopyProperty_iff R G _).2
    ⟨W, ⟨dgGluingShiftModuleHomotopyIso R C D M X n p q⟩⟩

omit p q in
/-- 元の両圏の前三角性だけを明示入力として、全整数シフトの表現可能性を供給。 -/
lemma dgGluingChosenShiftHomotopyRepresentable
    (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D) :
    dgHomotopyRepresentable R G (shiftModule n (representable R X)) :=
  dgGluingShiftHomotopyRepresentable R C D M X n
    (dgGluingChooseShiftRepresentative R C X.left n hC)
    (dgGluingChooseShiftRepresentative R D X.right n hD)

end SerrePositivity.InfinityCategories
