module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Completion

/-! # H⁰ の環構造と単位付き導来極限錐のデータ

概要：底の導来対象と無関係な環構造を許さず、辺と射影の乗法整合性を記録する。
方針：通常の R 代数の関手と加群の比較同型を持ち、実際の join 錐の脚を照合する。
規約：単位との両立は図式上の slice の辺として保持する。
使われ方：E3 界面の h0 と limitCone の型。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R]

/-- H⁰ の環・辺・単位を、底の導来加群のデータに結び付ける。 -/
structure H0RingData (P : algebraNerve R ⟶ derivedInfinityCategory R)
    (η : NatInfinity R (J R) P) where
  /-- H⁰ の通常の R 代数の関手。 -/
  ringFunctor : A_R R ⥤ A_R R
  /-- 元の加群構造との指定同型。 -/
  moduleIso : ∀ S, (discreteAlgebraModule R).obj (ringFunctor.obj S) ≅ H R 0 (vertex R P S)
  /-- 代数の射の底は同じ辺の H⁰ と一致する。 -/
  map_compat : ∀ {S T} (f : S ⟶ T),
    (discreteAlgebraModule R).map (ringFunctor.map f) ≫ (moduleIso T).hom =
      (moduleIso S).hom ≫ HMap R 0 (edge R P f)
  /-- H⁰ の環準同型としての自然な単位。 -/
  unit : 𝟭 (A_R R) ⟶ ringFunctor
  /-- 環の単位は、単体的単位の成分の H⁰ そのもの。 -/
  unit_compat : ∀ S,
    (JHZeroIso R S).hom ≫ (discreteAlgebraModule R).map (unit.app S) ≫ (moduleIso S).hom =
      HMap R 0 (component R η S)

/-- join の左頂点から指定した右頂点へ向かう、一単体の標準表示。 -/
def joinLegSimplex {K : SSet.{u + 1}} (x : K _⦋0⦌) : (join (Δ[0] : SSet.{u + 1}) K) _⦋1⦌ :=
  ⟨⟨1, by decide⟩, SSet.yonedaEquiv (𝟙 Δ[0]), x⟩

/-- 指定された S → T を R 上の代数の射として使う。 -/
def targetUnitMap (p : ℕ) [Fact p.Prime] (S : A_R R) (T : PerfUnder_u p S.right) :
    S ⟶ (targetAlgebra R p S).obj T := Under.homMk T.obj.hom rfl

/-- S から perfectoid 標的への射は標的圏の射について自然。 -/
theorem targetUnitMap_naturality (p : ℕ) [Fact p.Prime] (S : A_R R)
    {T U : PerfUnder_u p S.right} (f : T ⟶ U) :
    targetUnitMap R p S T ≫ (targetAlgebra R p S).map f = targetUnitMap R p S U := by
  ext1
  exact Under.w f.hom

/-- Prop 8.5 の特定の錐と、単位・環の射影との整合性。極限性は別の欄で受け取る。 -/
structure BSLimitConeData (p : ℕ) [Fact p.Prime]
    (P : algebraNerve R ⟶ derivedInfinityCategory R) (η : NatInfinity R (J R) P)
    (h0 : H0RingData R P η) (S : A_R R) where
  /-- Type u の標的だけを添字とする導来錐。 -/
  cone : JoinCone (targetDiagram R p S)
  /-- 錐の頂点は指定された perfectoid 化。 -/
  vertex_eq : cone.vertex = vertex R P S
  /-- 通常の代数圏での、元の S から全標的への錐。 -/
  sourceCone : JoinCone (nerveMap (targetAlgebra R p S))
  /-- 通常の錐の頂点を元の S に固定する。 -/
  source_vertex : sourceCone.vertex = ComposableArrows.mk₀ S
  /-- 通常の錐の各脚は元の S → T そのもの。nerve 内なので高次の合成もこれで固定される。 -/
  source_legs : ∀ T, sourceCone.val.app _ (joinLegSimplex (ComposableArrows.mk₀ T)) =
    ComposableArrows.mk₁ (targetUnitMap R p S T)
  /-- 図式上の錐の間の辺として単位による因子分解を保持する。 -/
  overSource : (sliceOver (targetDiagram R p S)).Edge (sourceCone.postcomp (J R)) cone
  /-- その辺の頂点への射影は、元の単体的単位の成分。 -/
  overSource_unit : (overSource.map (sliceOverProjection (targetDiagram R p S))).edge =
    (component R η S).edge
  /-- 実際の導来錐の脚を、両端を固定した辺として保持する。 -/
  projectionEdge : ∀ T : PerfUnder_u p S.right,
    (derivedInfinityCategory R).Edge (vertex R P S) (vertex R (J R) ((targetAlgebra R p S).obj T))
  /-- 脚は任意に添えた辺でなく、join 錐の実際の一単体。 -/
  projectionEdge_eq : ∀ T, (projectionEdge T).edge =
    cone.val.app _ (joinLegSimplex (ComposableArrows.mk₀ T))
  /-- H⁰ 上の射影は環準同型である。 -/
  projection : ∀ T : PerfUnder_u p S.right, h0.ringFunctor.obj S ⟶ (targetAlgebra R p S).obj T
  /-- 各射影は元の単位との三角形を可換にする。 -/
  projection_unit : ∀ T, h0.unit.app S ≫ projection T = targetUnitMap R p S T
  /-- 環の射影は標的について自然。 -/
  projection_naturality : ∀ {T U : PerfUnder_u p S.right} (f : T ⟶ U),
    projection T ≫ (targetAlgebra R p S).map f = projection U
  /-- 射影の底の線形写像は、指定した導来錐の脚の H⁰ と一致する。 -/
  projection_compat : ∀ T,
    (h0.moduleIso S).hom ≫ HMap R 0 (projectionEdge T) ≫
        (JHZeroIso R ((targetAlgebra R p S).obj T)).hom =
      (discreteAlgebraModule R).map (projection T)

end SerrePositivity.BhattScholze.PerfectoidizationInterface
