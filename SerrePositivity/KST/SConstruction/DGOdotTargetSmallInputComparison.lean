module
public import SerrePositivity.KST.SConstruction.DGUniverseLiftClosedFamily
public import SerrePositivity.KST.SConstruction.DGKInputClosedComparison
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallInput

/-! # 同じ cone 作用と比較代数射を結ぶ固定 S 内の実二単体
概要：元の全 Hom 自然な cone 同型を同じ固定 S の native Hom に保持する。
方針：対象宇宙だけを持ち上げ、元の Hom end の同型から指定三辺の二単体を選ぶ。
規約：ν 像と元の Perf 比較の追加照合は未主張。使われ方：相対 K-10 の終域比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 同じ実 cone 作用を、同じ固定 S の元の厳密 dg 辺として保持する。 -/
def dgOdotConeAlgebraSmallInputMap : dgOdotAlgebraInput R d ⟶ dgOdotTargetSmallInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, 0, u + 1, u + 1, u + 1}
    (dgOdotConeAlgebraSmallFunctor R d))

/-- 元の cone 比較の同じ順逆成分を、持ち上げた実入力 Hom end の閉同型にする。 -/
def dgOdotAlgebraSmallInputIso :
    ForgetEnrichment.of (Complex R) (dgOdotConeAlgebraSmallInputMap R d).down ≅
    ForgetEnrichment.of (Complex R) (dgOdotTargetAlgebraSmallInputMap R d).down :=
  dgUniverseLiftFunctorClosedIso R (DGOdotTargetSmallPerfect R d)
    (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d))
    (dgOdotConeAlgebraSmallFunctor R d) (dgOdotTargetAlgebraSmallFunctor R d)
    (fun _ => dgOdotTargetSmallPointIso R d) (dgOdotAlgebraSmallPointIso_naturality R d)

/-- 同じ指定閉同型の元の実辺を、固定 S の native Hom 内に保持する。 -/
def dgOdotAlgebraSmallInputHomEdge :=
  dgKInputClosedIsoHomEdge R (dgOdotConeAlgebraSmallInputMap R d)
    (dgOdotTargetAlgebraSmallInputMap R d) (dgOdotAlgebraSmallInputIso R d)

/-- 同じ元の native 辺を標準区間比較へ写した、固定 S 内の実四角形。 -/
def dgOdotAlgebraSmallInputSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R :=
  dgKInputClosedIsoSquare R _ _ (dgOdotAlgebraSmallInputIso R d)

/-- 元の native 辺を保つ同じ標準比較四角形全体の ν 像。 -/
def dgOdotAlgebraSmallNuSquare := dgOdotAlgebraSmallInputSquare R d ≫ dgKInputNu R

/-- 元の native 辺を保つ同じ標準比較四角形全体の K 像。 -/
def dgOdotAlgebraSmallKSquare := dgOdotAlgebraSmallInputSquare R d ≫ dgKInputK R

/-- 同じ固定 S 内で、元の cone 作用と元の比較代数射の合成作用を結ぶ実二単体。 -/
def dgOdotAlgebraSmallInputComparison :
    Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotConeAlgebraSmallInputMap R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 (dgOdotTargetSmallInput R d)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetAlgebraSmallInputMap R d)) :=
  dgKInputClosedIsoTriangle R _ _ (dgOdotAlgebraSmallInputIso R d)

/-- 同じ選択した実比較二単体を、固定 ν へ写す。 -/
def dgOdotAlgebraSmallNuComparison :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotConeAlgebraSmallInputMap R d)).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 (dgOdotTargetSmallInput R d))).map (dgKInputNu R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetAlgebraSmallInputMap R d)).map (dgKInputNu R)) :=
  (dgOdotAlgebraSmallInputComparison R d).map (dgKInputNu R)

/-- 同じ選択した実比較二単体を、固定 K へ写す。 -/
def dgOdotAlgebraSmallKComparison :
    Edge.CompStruct ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotConeAlgebraSmallInputMap R d)).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 (dgOdotTargetSmallInput R d))).map (dgKInputK R))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgOdotTargetAlgebraSmallInputMap R d)).map (dgKInputK R)) :=
  (dgOdotAlgebraSmallInputComparison R d).map (dgKInputK R)

end SerrePositivity.KST.SConstruction
