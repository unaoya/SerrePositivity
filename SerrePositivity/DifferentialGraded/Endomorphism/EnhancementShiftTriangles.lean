module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectShiftTriangles
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementTriangulated

/-! # U13 enhancementとの比較正方形の整合的shiftと三角性 -/
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

local instance : (perfectEndomorphismHomToPerfect A D S E hgen).CommShift ℤ :=
  perfectEndomorphismHomCommShift A D S E hgen
local instance : (perfectEndomorphismHomToPerfect A D S E hgen).IsTriangulated :=
  perfectEndomorphismHomIsTriangulated A D S E hgen

/-- 実際のdg比較のH⁰に、U13比較を通して主Perfと整合するshiftを入れる。 -/
@[instance_reducible]
def perfectEndomorphismDGHomotopyCommShift :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.CommShift ℤ :=
  Functor.CommShift.ofComp (perfectEndomorphismDerivedComparison A D S E hgen) ℤ

local instance : (perfectEndomorphismDG A D S E hgen).onHomotopy.CommShift ℤ :=
  perfectEndomorphismDGHomotopyCommShift A D S E hgen

lemma perfectEndomorphismDerivedComparison_commShift :
    NatTrans.CommShift (perfectEndomorphismDerivedComparison A D S E hgen).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (perfectEndomorphismDerivedComparison A D S E hgen) ℤ

/-- U13との既存比較正方形を三角関手の正方形へ強化する。 -/
lemma perfectEndomorphismDGHomotopyIsTriangulated :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.IsTriangulated := by
  let := perfectEndomorphismDerivedComparison_commShift A D S E hgen
  exact (Functor.isTriangulated_iff_comp_right
    (perfectEndomorphismDerivedComparison A D S E hgen)).2 inferInstance

/-- enhancement比較と主Perf比較の、三角形の圏における自然な正方形。 -/
def perfectEndomorphismEnhancementTriangleSquareIso :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.mapTriangle ⋙
        (perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ).mapTriangle ≅
      (perfectDGModuleToPerfect A D S).mapTriangle ⋙
        (perfectEndomorphismHomToPerfect A D S E hgen).mapTriangle := by
  let := perfectEndomorphismDerivedComparison_commShift A D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismDerivedComparison A D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
