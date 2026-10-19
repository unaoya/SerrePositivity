module
public import SerrePositivity.KST.SConstruction.ArCofiberFamily

/-! # 任意の切断位置の Ar 四角形
概要：区間を切断位置 k の左右に分ける coherent な四角形の族を作る。
方針：各端点を min・恒等・定数 k・max に送る単調な正方形を nerve に移す。
規約：零角は同じ図式の (k,k)。使われ方：一般の Segal 分解の cofiber 四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断する一つの端点の四角形は min・恒等・定数・max の四隅を持つ。 -/
def cutEndpoint {n : ℕ} (k i : Fin (n + 1)) (x y : Fin 2) : Fin (n + 1) :=
  max (intervalStep (min i k) i (min_le_left _ _) x)
    (intervalStep (min i k) k (min_le_right _ _) y)

/-- 切断の端点は区間の端点と二つの時刻の全てについて単調。 -/
lemma cutEndpoint_mono {n : ℕ} (k : Fin (n + 1)) {i j : Fin (n + 1)}
    {x x' y y' : Fin 2} (hij : i ≤ j) (hx : x ≤ x') (hy : y ≤ y') :
    cutEndpoint k i x y ≤ cutEndpoint k j x' y' := by
  apply max_le_max
  · exact ((intervalStep (min i k) i (min_le_left _ _)).monotone hx).trans
      (intervalStep_mono_endpoints _ _ (min_le_min hij le_rfl) hij x')
  · exact ((intervalStep (min i k) k (min_le_right _ _)).monotone hy).trans
      (intervalStep_mono_endpoints _ _ (min_le_min hij le_rfl) le_rfl y')

/-- 切断四角形の左下角は左側への端点制限。 -/
lemma cutEndpoint_zero_zero {n : ℕ} (k i : Fin (n + 1)) :
    cutEndpoint k i 0 0 = min i k := by simp [cutEndpoint, intervalStep]

/-- 切断四角形の右下角は元の端点。 -/
lemma cutEndpoint_one_zero {n : ℕ} (k i : Fin (n + 1)) :
    cutEndpoint k i 1 0 = i := by simp [cutEndpoint, intervalStep]

/-- 切断四角形の左上角は切断位置自身。 -/
lemma cutEndpoint_zero_one {n : ℕ} (k i : Fin (n + 1)) :
    cutEndpoint k i 0 1 = k := by simp [cutEndpoint, intervalStep]

/-- 切断四角形の右上角は右側への端点制限。 -/
lemma cutEndpoint_one_one {n : ℕ} (k i : Fin (n + 1)) :
    cutEndpoint k i 1 1 = max i k := by simp [cutEndpoint, intervalStep]

/-- 任意の切断位置で全 Ar 区間を同時に四角形へ送る順序写像。 -/
def arCutSquareOrder (n : ℕ) (k : Fin (n + 1)) :
    Ar.{u} n × ULift.{u} (Fin 2 × Fin 2) →o Ar.{u} n where
  toFun p := arObj (cutEndpoint k p.1.down.val.1 p.2.down.1 p.2.down.2)
    (cutEndpoint k p.1.down.val.2 p.2.down.1 p.2.down.2)
    (cutEndpoint_mono k p.1.down.property le_rfl le_rfl)
  monotone' _a _b h := ⟨cutEndpoint_mono k h.1.1 h.2.1 h.2.2,
    cutEndpoint_mono k h.1.2 h.2.1 h.2.2⟩

/-- Ar の鎖と正方形の単体から切断四角形の鎖を作る。 -/
def arCutSquareChain {n d : ℕ} (k : Fin (n + 1))
    (s : (arNerve.{u} n ⊗ (Δ[1] ⊗ Δ[1] : SSet.{u})) _⦋d⦌) :
    ComposableArrows (Ar.{u} n) d :=
  (show Monotone (fun r : Fin (d + 1) => arCutSquareOrder n k
    (s.1.obj r, (ULift.up (prodStdSimplex.objEquiv s.2 r) : ULift.{u} (Fin 2 × Fin 2)))) from by
      intro r t h
      exact (arCutSquareOrder n k).monotone
        ⟨s.1.monotone h, (prodStdSimplex.objEquiv s.2).monotone h⟩).functor

/-- 全単体の族を保持する Ar[n] の切断四角形。 -/
def arCutSquareMap (n : ℕ) (k : Fin (n + 1)) :
    arNerve.{u} n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n where
  app _ := ↾fun s => arCutSquareChain k s
  naturality {_d _e} _α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun _ => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    rfl

/-- 一つの Ar 区間で切断四角形を評価した形状。 -/
def arCutSquareAt {n : ℕ} (k : Fin (n + 1)) (a : Ar.{u} n) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ arNerve n :=
  CartesianMonoidalCategory.lift (SSet.const (ComposableArrows.mk₀ a)) (𝟙 _) ≫ arCutSquareMap n k

end SerrePositivity.KST.SConstruction
