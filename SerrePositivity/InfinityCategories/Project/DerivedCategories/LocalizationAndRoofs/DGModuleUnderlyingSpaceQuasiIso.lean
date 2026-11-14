module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedCosliceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleUnderlyingCosliceTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleUnitLiftPostcomposition
/-!
概要：同じ基礎空間 ∞ 関手は、任意の加群の準同型の実辺を可逆な実辺へ送る。
方針：R の代表加群からの全 Hom 後合成の準同型性と、実 coslice 輸送の判定を結ぶ。
規約：終点の射影性も全加群の生の nerve での可逆性も仮定しない。
使われ方：実 augmentation の空間値比較の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ基礎空間 ∞ 関手は、元の同じ加群準同型の持ち上げた実辺を反転する。 -/
lemma dgHomUnderlyingSpaceInfinity_invertsQuasiIso {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R PUnit.{1} f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((SSet.Edge.ofTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R
            (_root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1})).onClosed.map f)))).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R D)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitPostcomp_lift_quasiIso R D f hf
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity_invertible_of_cosliceTransport R D
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedCosliceTransport_isQCatEquivalence R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map f)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
