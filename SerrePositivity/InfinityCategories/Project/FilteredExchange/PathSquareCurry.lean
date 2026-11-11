module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram

/-!
概要：path の全円柱の変形を、時間付きパラメータの path の族へ移す。
方針：path・パラメータ・時間を並べ替え、path 変数で curry する。
規約：path と時間を区別し、四つの端を厳密に回収する。
使われ方：二入力の輸送に整合する path 引き戻し内のホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：path・パラメータ・時間をパラメータ・path・時間へ並べ替える。
方針：各次数の直積の成分を並べ替える。
規約：最後の区間が時間。使われ方：全円柱の path 変数での curry。 -/
def pathSquareReorder (K : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (K ⊗ (Δ[1] : SSet.{u})) ⟶
      (K ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) where
  app _ := ↾fun x ↦ ((x.2.1, x.1), x.2.2)
  naturality {_ _} _ := rfl

/-- 概要：path の全円柱を時間付きパラメータの path の族へ移す。
方針：path を第一因子へ移して curry する。
規約：元の全円柱を保持。使われ方：引き戻し内の比較の path 座標。 -/
def pathSquareCurry {K X : SSet.{u}}
    (R : (K ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    K ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry (pathSquareReorder K ≫ R)

/-- 概要：path の指定端の評価は元の正方形の指定側辺。
方針：curry の評価式と成分の並べ替えを計算する。
規約：e は path の端。使われ方：輸送する二入力との整合。 -/
lemma pathSquareCurry_endpoint {K X : SSet.{u}}
    (R : (K ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶ X) (e : Fin 2) :
    pathSquareCurry R ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).app X =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint e K ≫ (β_ (Δ[1] : SSet.{u}) K).hom) ▷ (Δ[1] : SSet.{u})) ≫ R := by
  change curry (pathSquareReorder K ≫ R) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  rfl

/-- 概要：時間零で path の族を制限すると元の正方形の始端 path。
方針：uncurry の単射性と成分計算。規約：全 path。使われ方：比較の始端。 -/
lemma pathSquareCurry_zero {K X : SSet.{u}}
    (R : (K ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    SSet.ι₀ ≫ pathSquareCurry R =
      curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ SSet.ι₀ ≫ R) := by
  apply uncurry_injective
  rw [uncurry_natural_left, pathSquareCurry, uncurry_curry, uncurry_curry]
  rfl

/-- 概要：時間一で path の族を制限すると元の正方形の終端 path。
方針：uncurry の単射性と成分計算。規約：全 path。使われ方：比較の終端。 -/
lemma pathSquareCurry_one {K X : SSet.{u}}
    (R : (K ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶ X) :
    SSet.ι₁ ≫ pathSquareCurry R =
      curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ SSet.ι₁ ≫ R) := by
  apply uncurry_injective
  rw [uncurry_natural_left, pathSquareCurry, uncurry_curry, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
