module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTriangleComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectEquivalence
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 主Perf比較の整合的shift・三角性と包含図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

local instance : (endomorphismDerivedHom A D E.val E.property.1).CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E.val E.property.1
local instance : (endomorphismDerivedHom A D E.val E.property.1).IsTriangulated :=
  endomorphismDerivedHomIsTriangulated A D E.val E.property.1

/-- 既存の主Perf制限に、導来Homから制限した整合的shiftを入れる。 -/
@[instance_reducible]
def perfectEndomorphismHomCommShift :
    (perfectEndomorphismHomToPerfect A D S E hgen).CommShift ℤ := by
  unfold perfectEndomorphismHomToPerfect
  infer_instance

local instance : (perfectEndomorphismHomToPerfect A D S E hgen).CommShift ℤ :=
  perfectEndomorphismHomCommShift A D S E hgen

/-- 主Perf比較と主導来Homの包含正方形。 -/
def perfectEndomorphismHomInclusionIso :
    perfectEndomorphismHomToPerfect A D S E hgen ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      perfectModuleInclusion A D S ⋙ endomorphismDerivedHom A D E.val E.property.1 :=
  (modulePerfect A (EndomorphismObject E.val)).liftCompιIso _ _

lemma perfectEndomorphismHomInclusionIso_commShift :
    NatTrans.CommShift (perfectEndomorphismHomInclusionIso A D S E hgen).hom ℤ := by
  unfold perfectEndomorphismHomInclusionIso
  infer_instance

lemma perfectEndomorphismHomIsTriangulated :
    (perfectEndomorphismHomToPerfect A D S E hgen).IsTriangulated := by
  unfold perfectEndomorphismHomToPerfect
  infer_instance

/-- 包含正方形を三角形の圏上の自然な正方形として保持する。 -/
def perfectEndomorphismHomTriangleSquareIso :
    (perfectEndomorphismHomToPerfect A D S E hgen).mapTriangle ⋙
        (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ).mapTriangle ≅
      (perfectModuleInclusion A D S).mapTriangle ⋙
        (endomorphismDerivedHom A D E.val E.property.1).mapTriangle := by
  let := perfectEndomorphismHomInclusionIso_commShift A D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismHomInclusionIso A D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

local instance : (perfectEndomorphismEquivalence A D S E hgen).functor.CommShift ℤ :=
  perfectEndomorphismHomCommShift A D S E hgen

/-- 主Perf同値の逆関手には、随伴から一意に定まる整合的shiftを入れる。 -/
@[instance_reducible]
def perfectEndomorphismEquivalenceInverseCommShift :
    (perfectEndomorphismEquivalence A D S E hgen).inverse.CommShift ℤ :=
  (perfectEndomorphismEquivalence A D S E hgen).commShiftInverse ℤ

local instance : (perfectEndomorphismEquivalence A D S E hgen).inverse.CommShift ℤ :=
  perfectEndomorphismEquivalenceInverseCommShift A D S E hgen

lemma perfectEndomorphismEquivalence_commShift :
    (perfectEndomorphismEquivalence A D S E hgen).CommShift ℤ :=
  (perfectEndomorphismEquivalence A D S E hgen).commShift_of_functor ℤ

/-- 順・逆両関手が三角的である主Perf同値。 -/
lemma perfectEndomorphismEquivalence_isTriangulated :
    letI := perfectEndomorphismEquivalence_commShift A D S E hgen
    (perfectEndomorphismEquivalence A D S E hgen).IsTriangulated := by
  let := perfectEndomorphismEquivalence_commShift A D S E hgen
  exact Equivalence.IsTriangulated.mk' _ (perfectEndomorphismHomIsTriangulated A D S E hgen)

end SerrePositivity.DifferentialGraded
