module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeWholeEdgeSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalMappingOppositeComposition

/-!
概要：一定の頂点への前合成を、同じ頂点の評価と定値関手の族に厳密に因子化する。
方針：内部 Hom の uncurry と実際の評価射を照合する。
規約：形状に頂点や充填性を要求せず、全パラメータの等式を保持する。
使われ方：元の余錐変換の頂点辺を、同じ頂点辺の定値変換として回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 一点への前合成は、同じ点での評価と定値関手の族の合成そのもの。 -/
lemma preConstant_evaluation_factor {A K X : SSet.{u}} (a : A _⦋0⦌) :
    (pre (SSet.const a : K ⟶ A)).app X = evaluateFunctorAt a ≫ constantFunctorMap K X := by
  have he : evaluateFunctorAt (Y := X) a =
      lift (SSet.const a) (𝟙 ((ihom A).obj X)) ≫ (ihom.ev A).app X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  have hl : (SSet.const a : K ⟶ A) ▷ ((ihom A).obj X) =
      snd K ((ihom A).obj X) ≫ lift (SSet.const a) (𝟙 ((ihom A).obj X)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  have hu : uncurry ((pre (SSet.const a : K ⟶ A)).app X) =
      (SSet.const a : K ⟶ A) ▷ ((ihom A).obj X) ≫ (ihom.ev A).app X := by
    rw [uncurry_pre]
  apply uncurry_injective
  rw [hu, uncurry_natural_left, constantFunctorMap, uncurry_curry,
    whiskerLeft_snd, he, ← Category.assoc, hl, Category.assoc]

/-- 元の全余錐の頂点変換の全一単体は、同じ頂点評価辺の定値関手像。 -/
lemma coconeWholeEdgeTop_constant {K X : SSet.{u}} {p r : K ⟶ X}
    (q : JoinCocone p) (d : JoinCocone r)
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X))
      (functorVertex q.val) (functorVertex d.val)) :
    (coconeWholeEdgeTop q d e).edge = (constantFunctorMap K X).app (Opposite.op ⦋1⦌)
      ((evaluateFunctorAt (coconeRightApexVertex K)).app (Opposite.op ⦋1⦌) e.edge) :=
  congrArg (fun f => f.app (Opposite.op ⦋1⦌) e.edge)
    (preConstant_evaluation_factor (X := X) (K := K) (coconeRightApexVertex K))

end SerrePositivity.InfinityCategories.HomotopyLimits
