module

public import SerrePositivity.InfinityCategories.F1B.KanEquivalenceLiftingInvertible
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinRelativeTargetCartesian
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeCriterion
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinRelativeInitialBoundary

/-!
概要：一般の圏論的同値の右持ち上げ条件から相対 join の cartesian な標的を構成する。
方針：内部 Hom の可逆辺の持ち上げを各 fiber へ移し、底上の引き戻しの判定を使う。
規約：関手の制限の形の標的に限定しない。
使われ方：標準局所 U 余極限から一般の標的上で相対図式を組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：一般の右持ち上げ条件は全空間の後合成の各 fiber で可逆辺を持ち上げる。
方針：内部 Hom による保存、可逆区間の持ち上げ、fiber 同型による移送を合成する。
規約：元の射影 p に充填性は要求しない。
使われ方：相対 join の標的の cartesian 輸送の厳密化。 -/
lemma kanInvertibleTargetLifting_fiberPostcomp_of_lifting {K C D E : SSet.{u}}
    [Quasicategory E] (p : K ⟶ C) (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (c : C _⦋0⦌) : KanInvertibleTargetLifting (kanFiberwiseHomPostcompFiber p U c) :=
  KanInvertibleTargetLifting.map_iso
    (KanEquivalenceLifting.invertibleTargetLifting (hU.internalHom (vertexFiber p c)))
    (kanFiberwiseHomFiberIso p c D) (kanFiberwiseHomFiberIso p c E)
    (kanFiberwiseHomFiberIso_postcomp p c U)

/-- 概要：一般の右持ち上げ条件の上の相対 join の標的は底への cartesian fibration。
方針：後合成の内ホーン充填と各 fiber の可逆辺の持ち上げを底上の引き戻しへ渡す。
規約：底と両値域は quasicategory、元の p は cocartesian fibration。
使われ方：局所の相対普遍性を全空間の充填性へ移す標的の構造。 -/
lemma kanRelativeJoinRelativeProjection_cartesianFibration_of_lifting {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : KanEquivalenceLifting U) :
    CartesianFibration (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) := by
  have : InnerFibration (kanFiberwiseHomPostcomp p U) :=
    kanFiberwiseHomPostcomp_innerFibration p U hU
  exact kanCartesianFibration_pullback_over
    (kanFiberwiseHomProjection p D)
    (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) E)
    (kanFiberwiseHomProjection p E)
    (kanFiberwiseHomPostcomp p U) (kanFiberwiseHomPre (D := E) (kanRelativeJoinInlOver p))
    (kanFiberwiseHomPostcomp_projection p U)
    (kanFiberwiseHomPre_projection (kanRelativeJoinInlOver p))
    (kanFiberwiseHomPostcomp_preservesCartesianEdges p U)
    (kanRelativeJoinRestriction_preservesCartesianEdges p)
    (kanInvertibleTargetLifting_fiberPostcomp_of_lifting p U hU)

/-- 概要：標準の局所 U 余極限は一般の右持ち上げ条件の上で全空間の始点境界を充填する。
方針：標準局所条件を相対余錐充填へ移し、fiber の比較と cartesian 輸送による移送を合成する。
規約：U を関手の制限の形に表示することは要求しない。
使われ方：一般の標的上の coherent な相対 Kan 図式の各点での入力。 -/
lemma kanRelativeJoinRelative_initialBoundary_of_relativeColimit {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : KanEquivalenceLifting U)
    (c : C _⦋0⦌) {d : vertexFiber p c ⟶ D} {z : JoinCocone d}
    (hz : IsRelativeColimitCone U z) :
    InitialBoundaryLifting (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U)
      (((kanRelativeJoinCoconeFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
        (functorVertex z.val)).val) := by
  have : InnerFibration U := hU.innerFibration
  have : Mono (kanRelativeJoinInlOver p).left :=
    inferInstanceAs (Mono (relativeJoinInl p (𝟙 C)))
  have : CocartesianFibration (Over.mk p).hom := inferInstanceAs (CocartesianFibration p)
  have : CocartesianFibration (Over.mk (relativeJoinBaseProjection p (𝟙 C))).hom :=
    inferInstanceAs (CocartesianFibration (relativeJoinBaseProjection p (𝟙 C)))
  have : InnerFibration (kanFiberwiseHomPostcomp p U) :=
    kanFiberwiseHomPostcomp_innerFibration p U hU
  have : InnerFibration (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U) :=
    kanFiberwiseRelativeRestriction_innerFibration (kanRelativeJoinInlOver p) U hU
  have : CartesianFibration (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U) :=
    kanRelativeJoinRelativeProjection_cartesianFibration_of_lifting p U hU
  have : Quasicategory (KanFiberwiseRelativeTarget (kanRelativeJoinInlOver p) U) :=
    quasicategory_of_innerFibration (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U)
  exact kanInitialBoundaryLifting_of_fiber_map
    (kanFiberwiseHomProjection (relativeJoinBaseProjection p (𝟙 C)) D)
    (kanFiberwiseRelativeProjection (kanRelativeJoinInlOver p) U)
    (kanFiberwiseRelativeRestriction (kanRelativeJoinInlOver p) U)
    (kanFiberwiseRelativeRestriction_projection (kanRelativeJoinInlOver p) U)
    (kanRelativeJoinRelativeRestriction_preservesCartesianEdges p U) c _
    (kanRelativeJoinRelativeFiber_initialBoundary p c U
      (kanRelativeCoconeLifting_of_isRelativeColimitCone U z hz))

end SerrePositivity.InfinityCategories.F1B
