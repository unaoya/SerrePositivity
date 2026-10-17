module
public import SerrePositivity.InfinityCategories.Derived.Semifree
public import SerrePositivity.DifferentialGraded.Derived.SemifreeProjective
public import SerrePositivity.DifferentialGraded.Module.RingProjective

/-! # Semifree 複体の K-projective 性 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：semifree 複体は K-projective である。
方針：一点加群の semifree 射影性を、Hom 複体の比較を介して転送する。
規約：仮定は実際の filtration の存在のみ。使われ方：導来比較の充満忠実性。 -/
theorem complexSemifree_isKProjective {P : Complex S} (hP : complexSemifree S P) :
    P.IsKProjective :=
  (ringModule_homotopicallyProjective_iff S (ringModule S P)).mp
    (moduleSemifree_homotopicallyProjective S PUnit.{1} hP)

end SerrePositivity.InfinityCategories
