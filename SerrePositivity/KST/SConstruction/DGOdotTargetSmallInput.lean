module
public import SerrePositivity.KST.SConstruction.DGOdotTargetAlgebraSmallExtension
public import SerrePositivity.KST.SConstruction.DGOdotTargetInputTriangle

/-! # 元の終域と同じ cone 小模型を結ぶ固定 S 内の図式
概要：同じ小模型と厳密 Yoneda を固定 S に置き、元の比較代数射の因子分解を保持する。
方針：元の対象宇宙持ち上げと厳密合成保存を使い、実三角形を同じ ν/K へ写す。
規約：同じ厳密 dg 入力 S を維持。使われ方：相対 K-10 の終域比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 同じ評価済み cone 点を含む小模型を、同じ固定 S の対象宇宙に置く。 -/
def dgOdotTargetSmallInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (DGOdotTargetSmallPerfect R d)

/-- 元の終域から同じ小模型への厳密 Yoneda の、固定 S 内の同じ実辺。 -/
def dgOdotTargetSmallYonedaInputMap : dgOdotCornerInput R d ⟶ dgOdotTargetSmallInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, u + 1, u + 1, u + 1} (dgOdotTargetSmallYoneda R d))

/-- 元の比較代数射と同じ小模型の Yoneda の合成を、同じ固定 S の実辺にする。 -/
def dgOdotTargetAlgebraSmallInputMap : dgOdotAlgebraInput R d ⟶ dgOdotTargetSmallInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, u + 1, u + 1, u + 1}
    (dgOdotTargetAlgebraSmallFunctor R d))

/-- 同じ固定 S 内でも、元の比較代数射と Yoneda の実合成を厳密に回収する。 -/
lemma dgOdotTargetSmallInputMap_comp :
    dgOdotTargetInputMap R d ≫ dgOdotTargetSmallYonedaInputMap R d =
      dgOdotTargetAlgebraSmallInputMap R d := by
  apply ULift.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp.{u, 0, 0, u + 1, u + 1, u + 1, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (dgOdotTargetMap R d)) (dgOdotTargetSmallYoneda R d)).symm

/-- 元の終域と同じ実小模型の比較を保つ、固定 S 内の実三角形。 -/
def dgOdotTargetSmallInputTriangle :
    Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetSmallYonedaInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetAlgebraSmallInputMap R d)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (dgOdotTargetInputMap R d) (dgOdotTargetSmallYonedaInputMap R d)
  rw [dgOdotTargetSmallInputMap_comp] at h
  exact h

/-- 同じ固定 S 内の元の実三角形の ν 像。 -/
def dgOdotTargetSmallNuTriangle :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetSmallYonedaInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetAlgebraSmallInputMap R d)).map (dgKInputNu R)) :=
  (dgOdotTargetSmallInputTriangle R d).map (dgKInputNu R)

/-- 同じ固定 S 内の元の実三角形の K 像。Sp 内の実二単体を保持する。 -/
def dgOdotTargetSmallKTriangle :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetSmallYonedaInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetAlgebraSmallInputMap R d)).map (dgKInputK R)) :=
  (dgOdotTargetSmallInputTriangle R d).map (dgKInputK R)

end SerrePositivity.KST.SConstruction
