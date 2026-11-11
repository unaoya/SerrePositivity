module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VariableSourcePrismLiftSpace

/-!
概要：動く初期値を持つ全 lift prism の普遍評価と終点評価。
方針：相対内部 Hom の二射影を展開し、初期値と底の族の引き戻しを回収する。
規約：初期値の変動を残したまま全パラメーターの射を構成する。
使われ方：始点同値の空間全体での終点制限。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：普遍 lift の curry の始点は指定したデータの第一成分。
方針：引き戻し条件を第一射影で評価する。
規約：初期値は動いてよい。
使われ方：普遍 prism の初期条件。 -/
lemma prismLiftSpaceCurry_start {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K d ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d ≫ d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).fst := by
  have h := congrArg (fun v ↦ v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).fst)
    (pullback.condition (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π) (g := d))
  simpa only [Category.assoc, Functor.PullbackObjObj.π_fst, internalHom, Quiver.Hom.unop_op,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry] using h

/-- 概要：普遍 lift の curry の底は指定したデータの第二成分。
方針：引き戻し条件を第二射影で評価する。
規約：底の区間族も動いてよい。
使われ方：普遍 prism の底上の可換性。 -/
lemma prismLiftSpaceCurry_base {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K d ≫ (ihom (Δ[1] ⊗ K)).map p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K d ≫ d ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).snd := by
  have h := congrArg (fun v ↦ v ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).snd)
    (pullback.condition (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).π) (g := d))
  simpa only [Category.assoc, Functor.PullbackObjObj.π_snd, internalHom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry] using h

/-- 概要：動く初期値を持つ lift 空間の普遍 prism。
方針：第一射影の関手空間への射を展開して結合子で並べ直す。
規約：区間、係数、全 lift のパラメーターの順。
使われ方：動く始点同値に対する普遍的な lift の評価。 -/
def prismLiftSpacePrism {E B L : SSet.{u}} (p : E ⟶ B) (K : SSet.{u})
    (d : L ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).pt) :
    Δ[1] ⊗ (K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace p K d) ⟶ E :=
  (α_ Δ[1] K _).inv ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K d)

/-- 概要：普遍 prism の初期値は元の動く初期値の引き戻し。
方針：始点の curry の公式と初期値データの第一射影を展開する。
規約：初期値のパラメーター依存を保つ厳密な等式。
使われ方：始点同値の空間への射影と普遍評価の可換性。 -/
lemma prismLiftSpacePrism_start {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ prismLiftSpacePrism p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) =
      (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv)) ≫ v := by
  calc
    _ = uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K)).app E) := by
      rw [uncurry_pre_app]
      rfl
    _ = uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).fst) :=
      congrArg uncurry (prismLiftSpaceCurry_start p K _)
    _ = _ := by
      have h := congrArg (fun w ↦ uncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫ w))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData_fst p v δ hv)
      exact h.trans (by rw [uncurry_natural_left, uncurry_curry])

/-- 概要：普遍 prism の底は元の底の区間族の引き戻し。
方針：底の curry の公式と初期値データの第二射影を展開する。
規約：元の区間族の全パラメーターを保持する。
使われ方：動く始点の lift を同じ底の族に保つ。 -/
lemma prismLiftSpacePrism_base {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) :
    prismLiftSpacePrism p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫ p =
      (Δ[1] ◁ (K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv))) ≫ δ := by
  calc
    _ = (α_ Δ[1] K _).inv ≫ uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceCurry p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫
        (ihom (Δ[1] ⊗ K)).map p) := by
      rw [uncurry_natural_right]
      rfl
    _ = (α_ Δ[1] K _).inv ≫ uncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPrismRelativeHom p K).snd) :=
      congrArg (fun w ↦ (α_ Δ[1] K _).inv ≫ uncurry w) (prismLiftSpaceCurry_base p K _)
    _ = _ := by
      have h := congrArg (fun w ↦ (α_ Δ[1] K _).inv ≫ uncurry
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpaceProjection p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ≫ w))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData_snd p v δ hv)
      exact h.trans (by rw [uncurry_natural_left, uncurry_curry]; rfl)

/-- 概要：底の終点が固定されていれば普遍 prism の終点はその fiber に入る。
方針：底の引き戻しの式を終点で制限する。
規約：初期値は依然として動いてよい。
使われ方：終点評価の fiber 値の射の構成。 -/
lemma prismLiftSpacePrism_finish_base {E B K L : SSet.{u}} (p : E ⟶ B)
    (v : K ⊗ L ⟶ E) (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B)
    (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) (b : B _⦋0⦌)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ L) ≫ δ = SSet.const b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ prismLiftSpacePrism p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv)) ≫ p =
      SSet.const b := by
  rw [Category.assoc, prismLiftSpacePrism_base, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, h₁, SSet.comp_const]

/-- 概要：動く初期値の全 lift prism の終点を fiber 間の関手空間で評価する。
方針：終点を固定した底の fiber へ持ち上げて curry する。
規約：始点を動かすパラメーターを忘れない全空間上の射。
使われ方：Kerodon Lemma 5.6.9.1（Tag 02SN） の同時の終点制限。 -/
def prismLiftSpaceEndpoint {E B K L : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ δ) (b : B _⦋0⦌)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (K ⊗ L) ≫ δ = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftSpace p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv) ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ prismLiftSpacePrism p K (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismLiftData p v δ hv))
    (prismLiftSpacePrism_finish_base p v δ hv b h₁))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
