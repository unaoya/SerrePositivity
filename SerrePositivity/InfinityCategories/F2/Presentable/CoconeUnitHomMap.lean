module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeUnitHomNaturality
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeApexHomEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.ConstantEvaluationHomTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.InitialBoundaryHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeWholeEdgeNaturality

/-!
概要：native な余錐の単位が与える頂点からの Hom 対応。
方針：形状ホモトピーを端点の等式で輸送し、右頂点評価の自然性を使う。
規約：指定した全余錐とその頂点を保つ。
使われ方：選んだ余極限関手と定値図式の随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits SSet.Truncated.HomotopyCategory

/-- 概要：元の全余錐の図式から定値頂点への単位。
方針：形状の標準ホモトピーの像の両端を輸送する。
規約：元の図式と native な頂点を保つ。
使われ方：普遍余錐の Hom の表示。 -/
def coconeUnitHom {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    FunctorHom p (SSet.const c.vertex) :=
  F1B.kanFunctorHomCongr c.property (cocone_const_rightApex c)
    (homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coconeDomainHomotopy K) c.val)))

/-- 概要：余錐単位と頂点評価の合成は底制限そのもの。
方針：定値標的への前合成自然性と評価の定値化の公式を合わせる。
規約：元の全余錐からの指定 Hom を使う。
使われ方：単位による普遍 Hom 写像の全単射性。 -/
lemma coconeUnitHom_evaluation {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p)
    (y : X _⦋0⦌) (α : FunctorHom c.val (SSet.const y)) :
    coconeUnitHom c ≫ constantFunctorHomMap K
      (functorHomEvaluate α (coconeRightApexVertex K) ≫
        eqToHom (congrArg HomotopyCategory.mk (ssetConst_zero_apply y _))) =
    F1B.kanFunctorHomCongr c.property (SSet.comp_const (joinInl K Δ[0]) y)
      ((hoFunctor.map ((pre (joinInl K Δ[0])).app X)).toFunctor.map α) :=
  constantEndpointUnitHom_evaluation (coconeRightApexVertex K)
    (coconeDomainHomotopy K) c.val c.property y α

end SerrePositivity.InfinityCategories.F2.Presentable
