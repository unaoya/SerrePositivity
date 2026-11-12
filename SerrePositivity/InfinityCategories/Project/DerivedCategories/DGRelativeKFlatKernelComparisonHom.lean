module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationFunctorDescentHom
/-!
概要：K-flat 入力上の元の指定 kernel 比較の射を、同じ二つの経路で展開する。
方針：元の raw factor と降下の実ホモトピーの類を保つ。
規約：元の指定比較を変更しない。使われ方：K-flat 上の指定合成子の二経路の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
/-- 同じ半自由制限比較は、元の指定 raw factor の値そのものである。 -/
lemma dgKernelDerivedInfinity_relativeKFlatRestrictionIso_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso, Eq.mp, Eq.mpr]
  rfl
/-- K-flat 入力の指定比較の射は、元の raw factor と同じ変形円柱の後続像である。 -/
lemma dgRelativeKFlatKernelComparisonIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelComparisonIso R D E P).hom =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)).hom ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived R D E P))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelComparisonIso, Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso_hom]
/-- 通常 K-flat 作用への比較の射は、同じ元の比較の射を保持する。 -/
lemma dgRelativeKFlatKernelNerve_derivedIso_hom_heq (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelComparisonIso R D E P).hom := by
  have hi : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelComparisonIso R D E P) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso, Eq.mpr]
    rfl
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelComparisonIso R D E P) rfl
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_resolution R D E P hP) hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories
