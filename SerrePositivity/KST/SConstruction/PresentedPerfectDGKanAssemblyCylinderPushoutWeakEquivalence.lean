module
public import SerrePositivity.KST.SConstruction.PointedDoubleMappingCylinderWeakEquivalence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderMonomorphisms
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyLeftEquivalence

/-! # 同じ元の隣接段円柱押し出しの弱比較
概要：元の右標的から実押し出しへの包含は局所化可逆で、元の組み立て四角形と可換。
方針：元の左脚の局所化可逆性を同じ実円柱押し出しの一般定理へ適用する。
規約：左標的比較そのものの弱同値性は主張しない。使われ方：BF 構造射の弱比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 元の右標的から同じ実円柱押し出しへの包含は、局所化で可逆。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutRightMap_localized_isIso (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C).right) := by
  let _ := presentedPerfectDGKanAssemblyLeftMap_localized_isIso A r C
  exact pointedDoubleMappingCylinderRight_localized_isIso
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C)
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyRightMap A r C)

/-- 元の二脚と実円柱押し出しの両標的比較は、局所化で厳密に可換。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushout_localized_square (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    AnodyneHomotopy.anodyneQ.map
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyLeftMap A r C).right ≫
        AnodyneHomotopy.anodyneQ.map
          (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
            ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
              presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r C).right =
      AnodyneHomotopy.anodyneQ.map
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyRightMap A r C).right ≫
        AnodyneHomotopy.anodyneQ.map
          (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
            ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
              presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C).right :=
  pointedDoubleMappingCylinder_localized_square
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C)
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyRightMap A r C)

end SerrePositivity.KST.SConstruction
