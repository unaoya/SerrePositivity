module
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingCosliceTransport
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitLiftPostcomposition
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ基礎空間 ∞ 関手は、元の同じ加群準同型の持ち上げた実辺を反転する。 -/
lemma dgHomUnderlyingSpaceInfinity_invertsQuasiIso {M N : RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N)
    (hf : moduleQuasiIso R PUnit.{1} f) :
    IsInvertibleEdge ((SSet.Edge.ofTruncated
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (dgClosedEdge R (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
          ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R
            (RightModule R PUnit.{1})).onClosed.map f)))).map
      (dgHomUnderlyingSpaceInfinity R D)) := by
  let := dgHomModuleUnitPostcomp_lift_quasiIso R D f hf
  apply dgHomUnderlyingSpaceInfinity_invertible_of_cosliceTransport R D
  exact dgClosedCosliceTransport_isQCatEquivalence R
    (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (dgHomModuleUnit R D) ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N)
    ((dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map f)
end SerrePositivity.InfinityCategories
