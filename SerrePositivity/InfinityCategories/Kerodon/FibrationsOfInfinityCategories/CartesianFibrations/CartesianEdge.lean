module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単体集合の射に関する cartesian・cocartesian 辺。
方針：指定辺を固定した外側ホーンの相対持ち上げ性を使う。
規約：辺は一単体で表し、ホーンの次元は n+2 とする。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、Definition 5.1.4.1（Tag 01UA） の fibration の基礎。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：p-cartesian 辺の外側ホーンによる定義。
方針：最後の辺が e の持ち上げ問題に解を要求する。
規約：p の inner fibration 性はこの定義に含めない。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、cartesian fibration の定義。 -/
@[kerodon 01T5]
def IsCartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X _⦋1⦌) : Prop :=
  ∀ (n : ℕ) (a : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ B),
    a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) = e →
    ∀ sq : CommSq a (horn (n + 2) (Fin.last (n + 2))).ι p b, sq.HasLift

/-- 概要：p-cocartesian 辺の外側ホーンによる定義。
方針：最初の辺が e の持ち上げ問題に解を要求する。
規約：p の inner fibration 性はこの定義に含めない。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、cocartesian fibration の定義。 -/
@[kerodon 01T5]
def IsCocartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X _⦋1⦌) : Prop :=
  ∀ (n : ℕ) (a : (horn (n + 2) 0 : SSet.{u}) ⟶ X)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ B),
    a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) = e →
    ∀ sq : CommSq a (horn (n + 2) 0).ι p b, sq.HasLift

/-- 概要：right fibration の全ての辺は cartesian。
方針：右ホーン包含の rlp を適用する。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、A2d と cartesian 辺の接続。 -/
lemma isCartesianEdge_of_rightFibration {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (e : X _⦋1⦌) : IsCartesianEdge p e := by
  intro n a b _ sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro (Fin.last (n + 2)) (by
      change (0 : ℕ) < n + 2
      omega))
  infer_instance

/-- 概要：left fibration の全ての辺は cocartesian。
方針：左ホーン包含の rlp を適用する。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Definition 5.1.1.1（Tag 01T5）、A2d と cocartesian 辺の接続。 -/
lemma isCocartesianEdge_of_leftFibration {X B : SSet.{u}} (p : X ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (e : X _⦋1⦌) : IsCocartesianEdge p e := by
  intro n a b _ sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro (0 : Fin (n + 3)) (by
      change (0 : ℕ) < n + 2
      omega))
  infer_instance

/-- 概要：二つの射に関して cartesian な辺は合成に関して cartesian。
方針：底の持ち上げを先に作り、その上で元のホーンを持ち上げる。
規約：二つ目の条件は p による辺の像に課す。
使われ方：Kerodon §5.1.1（Tag 01T4）、cartesian fibration の合成。 -/
lemma IsCartesianEdge.comp {X Y B : SSet.{u}} {p : X ⟶ Y} {q : Y ⟶ B}
    {e : X _⦋1⦌} (hp : IsCartesianEdge p e)
    (hq : IsCartesianEdge q (p.app (Opposite.op ⦋1⦌) e)) :
    IsCartesianEdge (p ≫ q) e := by
  intro n a b he sq
  have sq₁ : CommSq (a ≫ p) (horn (n + 2) (Fin.last (n + 2))).ι q b :=
    ⟨by simpa only [Category.assoc] using sq.w⟩
  have := hq n (a ≫ p) b (by change p.app _ (a.app _ _) = _; rw [he]) sq₁
  have sq₂ : CommSq a (horn (n + 2) (Fin.last (n + 2))).ι p sq₁.lift :=
    ⟨sq₁.fac_left.symm⟩
  have := hp n a sq₁.lift he sq₂
  exact CommSq.HasLift.mk' {
    l := sq₂.lift
    fac_left := sq₂.fac_left
    fac_right := by rw [← Category.assoc, sq₂.fac_right, sq₁.fac_right] }

/-- 概要：二つの射に関して cocartesian な辺は合成に関して cocartesian。
方針：底の持ち上げと全空間の持ち上げを順に作る。
規約：inner fibration 性を追加で仮定しない。
使われ方：Kerodon §5.1.1（Tag 01T4）、cocartesian fibration の合成。 -/
lemma IsCocartesianEdge.comp {X Y B : SSet.{u}} {p : X ⟶ Y} {q : Y ⟶ B}
    {e : X _⦋1⦌} (hp : IsCocartesianEdge p e)
    (hq : IsCocartesianEdge q (p.app (Opposite.op ⦋1⦌) e)) :
    IsCocartesianEdge (p ≫ q) e := by
  intro n a b he sq
  have sq₁ : CommSq (a ≫ p) (horn (n + 2) 0).ι q b :=
    ⟨by simpa only [Category.assoc] using sq.w⟩
  have := hq n (a ≫ p) b (by change p.app _ (a.app _ _) = _; rw [he]) sq₁
  have sq₂ : CommSq a (horn (n + 2) 0).ι p sq₁.lift := ⟨sq₁.fac_left.symm⟩
  have := hp n a sq₁.lift he sq₂
  exact CommSq.HasLift.mk' {
    l := sq₂.lift
    fac_left := sq₂.fac_left
    fac_right := by rw [← Category.assoc, sq₂.fac_right, sq₁.fac_right] }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge
attribute [cite HTT "2.4.1.3" (partial := component) "仮定：任意の Cartesian edge の pullback（HTT の (2) と一致）。結論：isCartesianEdge_pullback はその同じ辺の Cartesian 性を保つので (2) に一致。また comp と、全対象が準圏という追加仮定下の cancellation は (3) の両方向を与える。(1) の全 iso と一般の simplicial sets での cancellation は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge.comp
attribute [cite HTT "2.4.1.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge
attribute [cite HTT "3.1.2.1" (partial := special) "仮定：Cartesian p と任意の K（Lean が強い：p を right fibration に限定）。結論：同じ ihom K による pK が right、従って Cartesian fibration となり一致。この場合は p と pK の全辺が Cartesian なので点ごとの iff も両辺が成立する。一般の Cartesian fibration の指数は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_of_rightFibration
attribute [cite HTT "3.2.2.12" (partial := special) "仮定：p:X→S は Cartesian、q:Y→Z は cocartesian（Lean が強い：S=Δ⁰、q を left fibration に限定）。結論：この場合は Y′=Fun(X,Y),Z′=Fun(X,Z) と取れ、q′ が left、従って cocartesian fibration となる。全 Y と Y′ の辺が cocartesian なので (2) の辺の条件も両側が成立し一致。一般の相対 q には拡張しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration
