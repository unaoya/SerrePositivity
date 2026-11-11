module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism

/-!
概要：関手空間の辺の prism を底の一点上で評価する。
方針：内部 Hom の評価と頂点の定値族を各次数で計算する。
規約：prism の追加パラメーターは任意の単体集合。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の fiber での作用の transport 表示。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：関手空間の辺を底の指定頂点で評価する。
方針：頂点評価による辺の像の端点を元の図式の値に揃える。
規約：端点を F(b)、G(b) として表示する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の fiber での作用の底の辺。 -/
def functorEdgeAt {B X : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Edge (X := (ihom B).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (b : B _⦋0⦌) : SSet.Edge (F.app _ b) (G.app _ b) :=
  (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b)).ofEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b G)

/-- 概要：底の一点に定値な prism の制限は、その点で評価した関手空間の辺の定値族。
方針：各次数の評価を計算し、同じ関手を同じ定値単体に適用することを確認する。
規約：A は定値な底の図式の定義域。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、変換の持ち上げを fiber 上の transport に移す底の式。 -/
lemma functorEdgePrism_const {B X A : SSet.{u}} {F G : B ⟶ X}
    (e : SSet.Edge (X := (ihom B).obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    (b : B _⦋0⦌) :
    (Δ[1] ◁ (SSet.const b : A ⟶ B)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgePrism e =
      fst (Δ[1] : SSet.{u}) A ≫
        SSet.yonedaEquiv.symm (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b)).edge := by
  change _ = fst (Δ[1] : SSet.{u}) A ≫
    SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋1⦌) e.edge)
  rw [← SSet.yonedaEquiv_symm_comp]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  rfl

/-- 概要：追加パラメーター付き prism の底の一点への制限は、その点での評価の族。
方針：三成分の各次数の評価を計算する。
規約：追加パラメーター L 全体を保持する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間全体の fiber 上の作用の底の式。 -/
lemma functorParameterizedPrism_const {K B A L X : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj X) (b : B _⦋0⦌) :
    ((K ◁ (SSet.const b : A ⟶ B)) ▷ L) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H =
      (fst K A ▷ L) ≫ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨k, a⟩, l⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
