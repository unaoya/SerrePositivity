module
public import SerrePositivity.KST.SConstruction.DGKUniverseInput
public import SerrePositivity.KST.SConstruction.DGOdotRightQuotientComparison

/-! # 元の右代数・⊙・対角商の固定 S 内の三角形
概要：同じ対象宇宙に実入力を置き、元の右辺因子分解を S 内の実二単体にする。
方針：D の対象宇宙持ち上げの厳密合成則と、元の dg 因子分解を使う。
規約：Tamme 長方形全体やその ν 像は未構成。使われ方：相対 K-10 の右三角形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 元の右代数の右加群用圏を、共通対象宇宙の同じ S に置く。 -/
def dgOdotRightInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right)

/-- 元の商 End 代数の右加群用圏を、同じ S に置く。 -/
def dgOdotAlgebraInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d))

/-- 元の実対角商を、同じ S に置く。 -/
def dgOdotQuotientInputVertex : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (dgOdotQuotientInput R d).quotientObject

/-- 元の右代数射の全 Hom を保持する、同じ S 内の通常射。 -/
def dgOdotRightInputMap : dgOdotRightInput R d ⟶ dgOdotAlgebraInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, 0, u + 1, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotRightMap R d)))

/-- 元の代数から商への実射の全 Hom を保持する、同じ S 内の通常射。 -/
def dgOdotQuotientInputMap : dgOdotAlgebraInput R d ⟶ dgOdotQuotientInputVertex R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, u + 1, u + 1, u + 1}
    (dgOdotAlgebraToQuotient R d))

/-- 元の右 End 射を商へ送る実射を、同じ S 内の通常射として保持する。 -/
def dgOdotOriginalRightInputMap : dgOdotRightInput R d ⟶ dgOdotQuotientInputVertex R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, u + 1, u + 1, u + 1}
    (dgOdotOriginalRightToQuotient R d))

/-- 同じ固定入力 S でも、元の右辺の厳密な因子分解を回収する。 -/
lemma dgOdotRightInputMap_comp :
    dgOdotRightInputMap R d ≫ dgOdotQuotientInputMap R d = dgOdotOriginalRightInputMap R d := by
  apply ULift.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp.{u, 0, 0, u + 1, u + 1, u + 1, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotRightMap R d)) (dgOdotAlgebraToQuotient R d)).symm.trans
      (congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, u + 1, u + 1, u + 1} F)
        (dgOdotRightMap_toQuotient R d))

/-- 元の右辺と元の合成辺を保つ、固定 S 内の実二単体。 -/
def dgOdotRightInputTriangle :
    Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotRightInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotQuotientInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotOriginalRightInputMap R d)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgOdotRightInputMap R d) (dgOdotQuotientInputMap R d)
  rw [dgOdotRightInputMap_comp] at h
  exact h

/-- 同じ元の二単体の ν 像。元の二辺と合成辺をそのまま写す。 -/
def dgOdotRightNuTriangle :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotRightInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotQuotientInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotOriginalRightInputMap R d)).map (dgKInputNu R)) :=
  (dgOdotRightInputTriangle R d).map (dgKInputNu R)

/-- 同じ元の二単体の K 像。π 群ごとの比較ではなく Sp 内の実二単体。 -/
def dgOdotRightKTriangle :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotRightInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotQuotientInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotOriginalRightInputMap R d)).map (dgKInputK R)) :=
  (dgOdotRightInputTriangle R d).map (dgKInputK R)

end SerrePositivity.KST.SConstruction
