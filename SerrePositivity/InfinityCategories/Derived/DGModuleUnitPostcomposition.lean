module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnitPinchedModel
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso
/-!
概要：R の代表加群からの実 pinched Hom の後合成は、加群の準同型を全空間同値へ送る。
方針：代表加群の射影性で全 Hom 鎖写像の準同型性を示し、実 pinched 空間に送る。
規約：終点加群の射影性は不要。使われ方：実 augmentation の点ごとの空間同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ R の代表加群からの pinched Hom の、実閉射による後合成。 -/
def dgHomModuleUnitPostcomposition {M N : RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N) :
    DGNerve.pinchedHom R (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) ⟶
    DGNerve.pinchedHom R (DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (dgHomModuleUnit R D) ((dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N) :=
  pinchedHomChainMap (A := R)
    (D := DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (E := DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (x := dgHomModuleUnit R D) (y := (dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    (x' := dgHomModuleUnit R D) (y' := (dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N)
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f)
/-- 加群の準同型は、同じ実 pinched 後合成の全空間同値を誘導する。 -/
lemma dgHomModuleUnitPostcomposition_isQCatEquivalence {M N : RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N)
    (hf : moduleQuasiIso R PUnit.{1} f) :
    IsQCatEquivalence (dgHomModuleUnitPostcomposition R D f) := by
  let := moduleHomotopicallyProjective_postcompose_quasiIso R PUnit.{1}
    (representable_homotopicallyProjective R PUnit.{1} PUnit.unit) f hf
  exact (pinchedHomChainMap_quasiIso_equivalence (A := R)
    (D := DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (E := DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (x := dgHomModuleUnit R D) (y := (dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    (x' := dgHomModuleUnit R D) (y' := (dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N)
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (representable R PUnit.unit)) f)).isQCatEquivalence
end SerrePositivity.InfinityCategories
