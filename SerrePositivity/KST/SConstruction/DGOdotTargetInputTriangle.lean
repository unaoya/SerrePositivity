module
public import SerrePositivity.KST.SConstruction.DGOdotTargetAlgebra
public import SerrePositivity.KST.SConstruction.DGOdotInputTriangle

/-! # 元の右代数・⊙・終域代数の固定 S 内の三角形
概要：同じ実比較代数射を固定 S に置き、元の右辺の因子分解を実二単体として保持する。
方針：元の代数射の厳密可換性と、既存の宇宙持ち上げ・coherent nerve の関手性を使う。
規約：一般 StableCategory 上の K を使わない。使われ方：相対 K-10 の終域比較の右面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 元の終域代数の右加群用圏を、同じ共通対象宇宙の固定 S に置く。 -/
def dgOdotCornerInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, 0, u + 1} R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner)

/-- 元の ⊙ 比較射の全 Hom を保持する、固定 S 内の通常射。 -/
def dgOdotTargetInputMap : dgOdotAlgebraInput R d ⟶ dgOdotCornerInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, 0, u + 1, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)))

/-- 元の四角形の右辺の代数射を、そのまま同じ S 内の通常射として保持する。 -/
def dgOdotUpperInputMap : dgOdotRightInput R d ⟶ dgOdotCornerInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, 0, u + 1, u + 1} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper))

/-- 固定 S 内の ⊙ 経由の合成も、元の四角形の右辺を厳密に回収する。 -/
lemma dgOdotTargetInputMap_comp :
    dgOdotRightInputMap R d ≫ dgOdotTargetInputMap R d = dgOdotUpperInputMap R d := by
  apply ULift.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp.{u, 0, 0, u + 1, u + 1, u + 1, 0}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotRightMap R d)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d))).symm.trans
      (congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, 0, u + 1, u + 1} F)
        ((LocalizingInvariants.DGAlgebra.dgAlgebraMap_comp R
          (dgOdotRightMap R d) (dgOdotTargetMap R d)).trans
            (congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R) (dgOdotTargetMap_right R d))))

/-- 元の右辺を合成辺に保持する、固定 S 内の実二単体。 -/
def dgOdotTargetInputTriangle :
    Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotRightInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotUpperInputMap R d)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgOdotRightInputMap R d) (dgOdotTargetInputMap R d)
  rw [dgOdotTargetInputMap_comp] at h
  exact h

/-- 同じ元の比較二単体の ν 像。 -/
def dgOdotTargetNuTriangle :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotRightInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotUpperInputMap R d)).map (dgKInputNu R)) :=
  (dgOdotTargetInputTriangle R d).map (dgKInputNu R)

/-- 同じ元の比較二単体の K 像。Sp 内の全二単体として保持する。 -/
def dgOdotTargetKTriangle :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotRightInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotUpperInputMap R d)).map (dgKInputK R)) :=
  (dgOdotTargetInputTriangle R d).map (dgKInputK R)

end SerrePositivity.KST.SConstruction
