module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorCospanCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality

/-!
概要：元の全関手 cospan 錐の評価は、同じ二三角形の native な cospan 錐そのもの。
方針：元の左右の全二単体を厳密な pushout の一意性で照合する。
規約：辺の類だけでなく全錐の等号。使われ方：元の各点の極限性を a6 へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  {F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F X} {b : SSet.Homotopy F Y}
  {f : SSet.Homotopy X Z} {g : SSet.Homotopy Y Z} {d : SSet.Homotopy F Z}
  (L : FunctorCompositionTriangle a f d) (R : FunctorCompositionTriangle b g d)

/-- 元の coherent 表示の全 cospan 錐は、元の関手錐の同じ点での全評価と厳密に一致。 -/
lemma coherentCospanOfFunctorTriangles_pointwise_diagram (v : B _⦋0⦌) :
    coherentCospanConePointwiseDiagram F X Y Z (coherentCospanOfFunctorTriangles L R) v =
      functorCospanConeDiagram L R ≫ evaluateFunctorAt (ULift.up v) := by
  apply cospanCone_isPushout.hom_ext
  · rw [coherentCospanConePointwiseDiagram_left, ← Category.assoc,
      functorCospanConeDiagram_left]
    exact coherentCospanOfFunctorTriangles_left_point L R v
  · rw [coherentCospanConePointwiseDiagram_right, ← Category.assoc,
      functorCospanConeDiagram_right]
    exact coherentCospanOfFunctorTriangles_right_point L R v

/-- 元の各点の関手錐の極限性は、同じ全錐の coherent cospan 表示の極限性と同値。 -/
lemma coherentCospanOfFunctorTriangles_pointwise_isLimit_iff (v : B _⦋0⦌) :
    IsLimitCone (coherentCospanConePointwiseCone F X Y Z
      (coherentCospanOfFunctorTriangles L R) v) ↔
      IsLimitCone (evaluateFunctorCone (functorCospanCone L R) (ULift.up v)) :=
  isLimitCone_iff_of_cone_val_eq _ _
    (coherentCospanOfFunctorTriangles_pointwise_diagram L R v)

end SerrePositivity.InfinityCategories.F2
