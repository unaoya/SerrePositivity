module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace

/-!
概要：全 lift prism の空間の普遍 prism と終点評価。
方針：相対内部 Hom の引き戻しの普遍評価を展開し、指定した族と同じ始点・底を確認する。
規約：終点は元の輸送族の終点に固定せず、fiber 値の射として評価する。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の終点評価と普遍輸送の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：全 lift prism の空間に依存する普遍的な prism。
方針：全 prism の関手空間への射を展開し、区間を第一因子へ戻す。
規約：係数 K、lift のパラメーターの順に置く。
使われ方：終点評価を高次パラメーター全体の射として構成する。 -/
def FiberTransportFamily.liftSpacePrism {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) : Δ[1] ⊗ (K ⊗ T.liftSpace) ⟶ E :=
  (α_ Δ[1] K T.liftSpace).inv ≫ uncurry T.liftSpaceCurry

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpacePrism)


/-- 概要：普遍 lift prism と元の輸送族の引き戻しは同じ始点を持つ。
方針：相対内部 Hom の始点の式を展開する。
規約：全パラメーターの厳密な等式。
使われ方：終点作用の選択独立性に必要な共通の初期条件。 -/
lemma FiberTransportFamily.liftSpacePrism_start {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ T.liftSpacePrism =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ (T.precomp T.liftSpaceProjection).prism := by
  calc
    _ = uncurry (T.liftSpaceCurry ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E) := by
      rw [uncurry_pre_app]
      rfl
    _ = uncurry ((T.liftSpaceProjection ≫ T.prismCurry) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E) := congrArg uncurry T.liftSpaceCurry_start
    _ = _ := by
      rw [uncurry_pre_app, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily.prismCurry, uncurry_curry]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpacePrism_start)


/-- 概要：普遍 lift prism と元の輸送族の引き戻しは同じ底を持つ。
方針：相対内部 Hom の底の式を展開する。
規約：元の区間の族への合成を厳密に保つ。
使われ方：全 lift prism を同じ輸送族として比較する底の条件。 -/
lemma FiberTransportFamily.liftSpacePrism_base {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ) :
    T.liftSpacePrism ≫ p = (T.precomp T.liftSpaceProjection).prism ≫ p := by
  calc
    _ = (α_ Δ[1] K T.liftSpace).inv ≫
        uncurry (T.liftSpaceCurry ≫ (ihom (Δ[1] ⊗ K)).map p) := by
      rw [uncurry_natural_right]
      rfl
    _ = (α_ Δ[1] K T.liftSpace).inv ≫
        uncurry ((T.liftSpaceProjection ≫ T.prismCurry) ≫ (ihom (Δ[1] ⊗ K)).map p) :=
      congrArg (fun v ↦ (α_ Δ[1] K T.liftSpace).inv ≫ uncurry v) T.liftSpaceCurry_base
    _ = _ := by
      rw [uncurry_natural_right, uncurry_natural_left,
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily.prismCurry, uncurry_curry]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpacePrism_base)


/-- 概要：全 lift prism の普遍評価を一つの輸送族に束ねる。
方針：終点を fiber に持ち上げ、共通の始点と底の式を使う。
規約：終点は全 lift の選択に応じて変わる。
使われ方：終点評価と選択済み輸送の作用の全パラメーター上の比較。 -/
def FiberTransportFamily.liftSpaceTransportFamily {E B K L : SSet.{u}} {p : E ⟶ B}
    {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L ≫ γ = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f ((Δ[1] ◁ T.liftSpaceProjection) ≫ γ) := by
  let U := T.precomp T.liftSpaceProjection
  have hbase : T.liftSpacePrism ≫ p = (Δ[1] ◁ snd K T.liftSpace) ≫
      ((Δ[1] ◁ T.liftSpaceProjection) ≫ γ) :=
    T.liftSpacePrism_base.trans U.over_base
  have hend : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ T.liftSpace) ≫ T.liftSpacePrism) ≫ p = SSet.const b := by
    rw [Category.assoc, hbase]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.fiberTransportFamily_base_endpoint 1 _ b
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ T.liftSpacePrism) hend,
    T.liftSpacePrism, T.liftSpacePrism_start.trans U.start, rfl, hbase⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceTransportFamily)


/-- 概要：全 lift prism の終点評価は選択済み輸送の作用の引き戻しと関手同型。
方針：普遍評価と元の族を同じパラメーター上で比較し、curry の制限の公式を使う。
規約：全ての lift の高次パラメーターを同時に保持する。
使われ方：普遍輸送の同値性から中間空間の終点評価の同値性を得る。 -/
def FiberTransportFamily.liftSpaceEndpointIso {E B K L : SSet.{u}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌} {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a} {γ : Δ[1] ⊗ L ⟶ B}
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := b) p f γ)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 L ≫ γ = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (T.liftSpaceTransportFamily h₁).map (T.liftSpaceProjection ≫ T.map) := by
  have hbase : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 T.liftSpace ≫ ((Δ[1] ◁ T.liftSpaceProjection) ≫ γ) =
      SSet.const b := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const]
  have e := (T.liftSpaceTransportFamily h₁).mapIso p f _ hbase (T.precomp T.liftSpaceProjection)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily.precomp_map] at e
  exact e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamily (liftSpaceEndpointIso)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
