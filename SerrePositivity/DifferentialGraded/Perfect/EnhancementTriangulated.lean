module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementShift
public import SerrePositivity.DifferentialGraded.Category.TriangulatedTransport
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # 実際のdg shiftを備えたperfect H⁰の三角構造

構成済みの線形・shift同値で主Perfの三角構造を引き戻す。
標準dg cone三角形との比較と、小さい代表系への移送は別に検証する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主Perfの零対象を同値の逆関手で運び、H⁰に零対象を与える。 -/
instance perfectDGHomotopyHasZeroObject (S : Set D) :
    HasZeroObject (PerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonHasZeroObject (perfectDGModuleHomotopyEquivalence A D S)

/-- 主Perfでdistinguishedとなる三角形を引き戻し、既存の実際のdg shiftの下で各公理を満たす。 -/
instance perfectDGHomotopyPretriangulated (S : Set D) :
    Pretriangulated (PerfectDGHomotopyCategoryOver A D S) :=
  dgComparisonPretriangulated (perfectDGModuleHomotopyEquivalence A D S)

/-- H⁰の三角形のdistinguished性は、主Perfにおける比較像で判定できる。 -/
lemma perfectDGHomotopy_distinguished_iff (S : Set D)
    (T : Triangle (PerfectDGHomotopyCategoryOver A D S)) :
    T ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) ↔
      (perfectDGModuleToPerfect A D S).mapTriangle.obj T ∈
        distTriang (PerfectModuleCategoryOver A D S) := Iff.rfl

/-- 主Perfへの比較は三角関手。distinguishedクラスの引き戻しの定義から従う。 -/
instance perfectDGModuleToPerfectIsTriangulated (S : Set D) :
    (perfectDGModuleToPerfect A D S).IsTriangulated where
  map_distinguished _ hT := hT

/-- 主Perfへの完全忠実三角関手から、八面体公理を反映する。 -/
instance perfectDGHomotopyIsTriangulated (S : Set D) :
    IsTriangulated (PerfectDGHomotopyCategoryOver A D S) :=
  IsTriangulated.of_fully_faithful_triangulated_functor (perfectDGModuleToPerfect A D S)

/-- H⁰と主Perfの同値は、整数shiftに整合する三角同値である。 -/
instance perfectDGModuleHomotopyEquivalenceIsTriangulated (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (perfectDGModuleToPerfect A D S).IsTriangulated
    infer_instance)

end SerrePositivity.DifferentialGraded
