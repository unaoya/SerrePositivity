module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleQuasiIsoSurjectiveSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelComparisonInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 任意の双加群準同型に沿う、元の実導来作用の全関手同型。 -/
def dgKernelDerivedInfinity_mapIso_of_quasiIso
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D Q)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft_quasiIso R E D P Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanLeft_degree_surjective R E D P Q)).symm ≪≫
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_surjective_quasiIso R D E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight R E D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight_quasiIso R E D f hf)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleQuasiIsoSpanRight_degree_surjective R E D f)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
