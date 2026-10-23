module

public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：単体集合の射に関する cartesian・cocartesian 辺。
方針：指定辺を固定した外側ホーンの相対持ち上げ性を使う。
規約：辺は一単体で表し、ホーンの次元は n+2 とする。
使われ方：Kerodon Definition 5.1.1.1、Definition 5.1.4.1 の fibration の基礎。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：p-cartesian 辺の外側ホーンによる定義。
方針：最後の辺が e の持ち上げ問題に解を要求する。
規約：p の inner fibration 性はこの定義に含めない。
使われ方：Kerodon Definition 5.1.1.1、cartesian fibration の定義。 -/
def IsCartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X _⦋1⦌) : Prop :=
  ∀ (n : ℕ) (a : (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⟶ X)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ B),
    a.app (Opposite.op ⦋1⦌) (finalHornEdge n) = e →
    ∀ sq : CommSq a (horn (n + 2) (Fin.last (n + 2))).ι p b, sq.HasLift

/-- 概要：p-cocartesian 辺の外側ホーンによる定義。
方針：最初の辺が e の持ち上げ問題に解を要求する。
規約：p の inner fibration 性はこの定義に含めない。
使われ方：Kerodon Definition 5.1.1.1、cocartesian fibration の定義。 -/
def IsCocartesianEdge {X B : SSet.{u}} (p : X ⟶ B) (e : X _⦋1⦌) : Prop :=
  ∀ (n : ℕ) (a : (horn (n + 2) 0 : SSet.{u}) ⟶ X)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ B),
    a.app (Opposite.op ⦋1⦌) (initialHornEdge n) = e →
    ∀ sq : CommSq a (horn (n + 2) 0).ι p b, sq.HasLift

/-- 概要：right fibration の全ての辺は cartesian。
方針：右ホーン包含の rlp を適用する。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Definition 5.1.1.1、A2d と cartesian 辺の接続。 -/
lemma isCartesianEdge_of_rightFibration {X B : SSet.{u}} (p : X ⟶ B)
    [RightFibration p] (e : X _⦋1⦌) : IsCartesianEdge p e := by
  intro n a b _ sq
  have := RightFibration.mem (p := p) _
    (rightHornInclusions.intro (Fin.last (n + 2)) (by
      change (0 : ℕ) < n + 2
      omega))
  infer_instance

/-- 概要：left fibration の全ての辺は cocartesian。
方針：左ホーン包含の rlp を適用する。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Definition 5.1.1.1、A2d と cocartesian 辺の接続。 -/
lemma isCocartesianEdge_of_leftFibration {X B : SSet.{u}} (p : X ⟶ B)
    [LeftFibration p] (e : X _⦋1⦌) : IsCocartesianEdge p e := by
  intro n a b _ sq
  have := LeftFibration.mem (p := p) _
    (leftHornInclusions.intro (0 : Fin (n + 3)) (by
      change (0 : ℕ) < n + 2
      omega))
  infer_instance

/-- 概要：二つの射に関して cartesian な辺は合成に関して cartesian。
方針：底の持ち上げを先に作り、その上で元のホーンを持ち上げる。
規約：二つ目の条件は p による辺の像に課す。
使われ方：Kerodon §5.1.1、cartesian fibration の合成。 -/
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
使われ方：Kerodon §5.1.1、cocartesian fibration の合成。 -/
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

end SerrePositivity.InfinityCategories
