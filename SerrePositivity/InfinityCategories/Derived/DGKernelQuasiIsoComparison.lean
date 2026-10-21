module
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleQuasiIsoSurjectiveSpan
public import SerrePositivity.InfinityCategories.Derived.DGKernelComparisonInfinity
/-!
概要：任意の双加群準同型に沿い、元の実導来作用を全関手同型で比較する。
方針：元の射を回収する実切断を持つ共通 span の両脚へ、全射準同型の比較を適用する。
規約：元の射の全射性、局所 Hom の平坦性、元の tensor 出力の射影性は不要。
使われ方：一般双加群の導来作用の準同型不変性。比較の合成 coherence は別途必要。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 任意の双加群準同型に沿う、元の実導来作用の全関手同型。 -/
def dgKernelDerivedInfinity_mapIso_of_quasiIso
    {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R E D f) :
    FunctorIso (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q)) :=
  (dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (dgBimoduleQuasiIsoSpanLeft R E D P Q)
    (dgBimoduleQuasiIsoSpanLeft_quasiIso R E D P Q)
    (dgBimoduleQuasiIsoSpanLeft_degree_surjective R E D P Q)).symm ≪≫
  dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (dgBimoduleQuasiIsoSpanRight R E D f)
    (dgBimoduleQuasiIsoSpanRight_quasiIso R E D f hf)
    (dgBimoduleQuasiIsoSpanRight_degree_surjective R E D f)
end SerrePositivity.InfinityCategories
