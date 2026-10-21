module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelComparison
public import SerrePositivity.InfinityCategories.Derived.DeformationFunctorDescentHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D)
/-- 同じ半自由制限比較は、元の指定 raw factor の値そのものである。 -/
lemma dgKernelDerivedInfinity_relativeKFlatRestrictionIso_heq :
    HEq (dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P)
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
        (dgSemifreeKernelModuleDG R D E P)) := by
  simp only [dgKernelDerivedInfinity_relativeKFlatRestrictionIso, Eq.mp, Eq.mpr]
  rfl
/-- K-flat 入力の指定比較の射は、元の raw factor と同じ変形円柱の後続像である。 -/
lemma dgRelativeKFlatKernelComparisonIso_hom :
    (dgRelativeKFlatKernelComparisonIso R D E P).hom =
      ((dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P).precomp
        (dgRelativeKFlatResolution R D)).hom ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (deformationFunctorDescentHomotopy (dgRelativeKFlatResolution R D)
          (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatResolutionAugmentationHomotopy R D)
          (dgRelativeKFlatKernelToDerived R D E P))) := by
  rw [dgRelativeKFlatKernelComparisonIso, Iso.trans_hom, deformationFunctorDescentIso_hom]
/-- 通常 K-flat 作用への比較の射は、同じ元の比較の射を保持する。 -/
lemma dgRelativeKFlatKernelNerve_derivedIso_hom_heq (hP : Bimodule.rightRelativeKFlat R E D P) :
    HEq (dgRelativeKFlatKernelNerve_derivedIso R D E P hP).hom
      (dgRelativeKFlatKernelComparisonIso R D E P).hom := by
  have hi : HEq (dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
      (dgRelativeKFlatKernelComparisonIso R D E P) := by
    simp only [dgRelativeKFlatKernelNerve_derivedIso, Eq.mpr]
    rfl
  exact functorIso_hom_heq (dgRelativeKFlatKernelNerve_derivedIso R D E P hP)
    (dgRelativeKFlatKernelComparisonIso R D E P) rfl
    (dgRelativeKFlatKernelNerve_resolution R D E P hP) hi
end SerrePositivity.InfinityCategories
