module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotation
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConnectingConeSign
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationCancellation

/-!
概要：元全実逆回転比較の右包含制限と元負符号を保持する。
方針：元 cone shift descent の包含式と元 connecting 全比較の指定符号を合成する。
規約：同じ三因子の閉成分を使用する。
使われ方：元実逆回転後の指定上二単体。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "FS" => F.comp (moduleShiftDG R D 1)
local notation "GS" => G.comp (moduleShiftDG R D 1)
local notation "δ" => dgModuleNaturalConeConnecting R D F G η
local notation "CD" => dgModuleNaturalConeFunctor R D (CF) (FS) (δ)
local notation "S" => moduleShiftDG R D (-1)
local notation "L" => dgModuleNaturalInverseRotationSource R D F G η
local notation "α" => dgModuleNaturalInverseRotationConeShift R D F G η
local notation "β" => dgModuleNaturalInverseRotationShiftedComparison R D F G η
local notation "γ" => dgModuleNaturalInverseRotationCancellation R D G
local notation "ν" => dgModuleNaturalConeInr R D (CF) (FS) (δ)

/-- 概要：元全 cone shift 比較は元右包含の同じ実 shift を回収する。
方針：同じ元 descent の包含式と後合成の閉射回収を使う。
規約：元実包含の厳密等式。使われ方：全実逆回転の指定包含制限。 -/
lemma dgModuleNaturalInverseRotationConeShift_inr (x : P) :
    moduleConeInr R D
      (dgModuleNaturalConeArrow R D ((CF).comp (S)) ((FS).comp (S))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)) x) ≫
      dgModuleNaturalConeArrow R D (L) ((CD).comp (S)) (α) x =
        moduleShiftMap R D (-1)
          (moduleConeInr R D (dgModuleNaturalConeArrow R D (CF) (FS) (δ) x)) := by
  exact (dgModuleNaturalConeDesc_inr R D ((CF).comp (S)) ((FS).comp (S)) ((CD).comp (S))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ν) (S))
    (dgModuleNaturalConeShiftNull R D (CF) (FS) (δ) (-1))
    (dgModuleNaturalConeShiftComparison_boundary R D (CF) (FS) (δ) (-1))
    (dgModuleNaturalConeShiftNull_naturality R D (CF) (FS) (δ) (-1)) x).trans
      ((dgModuleNaturalConeShiftArrow R D (FS) (CD) (ν) (-1) x).trans
        (congrArg (moduleShiftMap R D (-1))
          (dgModuleNaturalConeInr_arrow R D (CF) (FS) (δ) x)))
end SerrePositivity.KST.SConstruction
