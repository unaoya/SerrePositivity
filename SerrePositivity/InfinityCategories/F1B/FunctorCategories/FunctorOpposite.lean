module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomotopyClasses
public import SerrePositivity.InfinityCategories.Core.PrismOpposite
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：指定ホモトピーと関手の同型の反転。
方針：区間の向きを交換する reversePrism と可逆な垂直辺の保存を使う。
規約：ホモトピーの向きと関手の同型の向きをともに交換する。
使われ方：右 Kan 拡張の相対 join 表示の円柱比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定したホモトピーを始域と標的について反転する。
方針：時間を第一因子へ直して reversePrism を取り、第二因子へ戻す。
規約：反転後の始点は元の終点の op。
使われ方：右指定自然変換を左側の表示に渡す。 -/
def homotopyOpposite {A Y : SSet.{u}} {f g : A ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.opFunctor.map g) (SSet.opFunctor.map f) where
  h := (β_ A.op (Δ[1] : SSet.{u})).hom ≫
    reversePrism ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)
  h₀ := by
    change prismEndpoint 0 A.op ≫ reversePrism ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) = _
    rw [reversePrism_endpoint]
    change SSet.opFunctor.map (prismEndpoint 1 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) = _
    rw [← Category.assoc, prismEndpoint_one_braiding, H.h₁]
    rfl
  h₁ := by
    change prismEndpoint 1 A.op ≫ reversePrism ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) = _
    rw [reversePrism_endpoint]
    change SSet.opFunctor.map (prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) = _
    rw [← Category.assoc, prismEndpoint_zero_braiding, H.h₀]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：関手の同型の代表の垂直辺は、第一因子を時間とする表示でも可逆。
方針：標準の区間の辺と頂点の定値辺を、型付きホモトピーの評価と同定する。
規約：同型の選んだ代表をそのまま使う。
使われ方：代表を反転したときの可逆性の入力。 -/
lemma functorIso_prism_vertical_isInvertible {A Y : SSet.{u}} [Quasicategory Y]
    {f g : A ⟶ Y} (e : FunctorIso f g) (a : A _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex
      (((β_ (Δ[1] : SSet.{u}) A).hom ≫ e.simplicialHomotopy.h).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant a 1))) := by
  have he : ((β_ (Δ[1] : SSet.{u}) A).hom ≫ e.simplicialHomotopy.h).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant a 1) =
      (simplicialHomotopyVertexEdge e.simplicialHomotopy a).edge := by
    change e.simplicialHomotopy.h.app (Opposite.op ⦋1⦌)
      (PinchedHom.constant a 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      e.simplicialHomotopy.h.app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge, homotopyIntervalEdge.edge)
    have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
      apply stdSimplex.ext
      intro j
      fin_cases j <;> rfl
    rw [pinchedConstant_one, hi]
  exact (isInvertibleEdge_congr he).2
    (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) a)

/-- 概要：平行な関手の同型を反対側の逆向きの関手の同型へ移す。
方針：代表の prism を反転し、点ごとの可逆性から関手の同型を作る。
規約：始域に quasicategory 性は不要。代表の類の写像の定義とは区別する。
使われ方：左相対 join 表示の一つの円柱比較を右側へ移す。 -/
def functorIsoOpposite {A Y : SSet.{u}} [Quasicategory Y] {f g : A ⟶ Y}
    (e : FunctorIso f g) : FunctorIso (SSet.opFunctor.map g) (SSet.opFunctor.map f) := by
  let J := (β_ (Δ[1] : SSet.{u}) A).hom ≫ e.simplicialHomotopy.h
  let H := reversePrism J
  have hv := reversePrism_vertical_isInvertible J (functorIso_prism_vertical_isInvertible e)
  have h₀ : prismEndpoint 0 A.op ≫ H = SSet.opFunctor.map g := by
    rw [reversePrism_endpoint]
    change SSet.opFunctor.map (prismEndpoint 1 A ≫ J) = _
    change SSet.opFunctor.map (prismEndpoint 1 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫
      e.simplicialHomotopy.h) = _
    rw [← Category.assoc, prismEndpoint_one_braiding, e.simplicialHomotopy.h₁]
  have h₁ : prismEndpoint 1 A.op ≫ H = SSet.opFunctor.map f := by
    rw [reversePrism_endpoint]
    change SSet.opFunctor.map (prismEndpoint 0 A ≫ J) = _
    change SSet.opFunctor.map (prismEndpoint 0 A ≫ (β_ (Δ[1] : SSet.{u}) A).hom ≫
      e.simplicialHomotopy.h) = _
    rw [← Category.assoc, prismEndpoint_zero_braiding, e.simplicialHomotopy.h₀]
  exact SerrePositivity.InfinityCategories.functorIsoTransport (functorIsoOfEquivalenceHomotopy H hv) h₀ h₁

end SerrePositivity.InfinityCategories
