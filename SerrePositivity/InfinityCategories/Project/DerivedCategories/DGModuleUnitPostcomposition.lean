module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnitPinchedModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Projective
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ R の代表加群からの pinched Hom の、実閉射による後合成。 -/
def dgHomModuleUnitPostcomposition {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (A := R)
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) (y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) (y' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N)
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit)) f)
/-- 加群の準同型は、同じ実 pinched 後合成の全空間同値を誘導する。 -/
lemma dgHomModuleUnitPostcomposition_isQCatEquivalence {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R PUnit.{1} f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgHomModuleUnitPostcomposition R D f) := by
  let := _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_postcompose_quasiIso R PUnit.{1}
    (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective R PUnit.{1} PUnit.unit) f hf
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_quasiIso_equivalence (A := R)
    (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) (y := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj M)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D) (y' := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})).obj N)
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit)) f)).isQCatEquivalence
end SerrePositivity.InfinityCategories.Project.DerivedCategories
