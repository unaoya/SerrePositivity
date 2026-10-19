module
public import SerrePositivity.KST.SConstruction.FiberResolutionCoordinates

/-! # 元の単体による fiber 解消の標準対象
概要：x∈X_n を (f(x),x,id) の因子分解対象に戻す。
方針：同じ標準単体上の strict pullback に Yoneda 射を持ち上げる。
規約：新しい fiber の充填や局所化仮定は使わない。使われ方：解消の augmentation の縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：元の n 単体を f(x) 上の標準左 fiber の n 単体へ戻す。
方針：Yoneda 射と恒等パラメーターで pullback に持ち上げる。
規約：元の単体と恒等射を厳密に保持。使われ方：解消の標準対象のラベル。 -/
def fiberResolutionCanonicalSimplex {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    (simplexLeftFiber f (f.app (Opposite.op ⦋n⦌) x)) _⦋n⦌ :=
  SSet.yonedaEquiv (simplexLeftFiberLift f (f.app (Opposite.op ⦋n⦌) x)
    (SSet.yonedaEquiv.symm x) (𝟙 (Δ[n] : SSet.{u})) (by
      rw [Category.id_comp, SSet.yonedaEquiv_symm_comp]))

/-- 概要：標準因子分解の元の単体は x。
方針：Yoneda 同値と pullback の第一射影。
規約：n 単体の厳密な等号。使われ方：augmentation と切断の合成。 -/
lemma fiberResolutionCanonicalSimplex_projection {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : X _⦋n⦌) :
    (simplexLeftFiberProjection f (f.app (Opposite.op ⦋n⦌) x)).app (Opposite.op ⦋n⦌)
      (fiberResolutionCanonicalSimplex f x) = x := by
  rw [fiberResolutionCanonicalSimplex, ← SSet.yonedaEquiv_comp,
    simplexLeftFiberLift_projection, Equiv.apply_symm_apply]

/-- 概要：標準因子分解のパラメーターは標準単体の恒等射。
方針：Yoneda 同値と pullback の第二射影。
規約：n 単体の厳密な等号。使われ方：標準対象からの因子分解射。 -/
lemma fiberResolutionCanonicalSimplex_parameter {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : X _⦋n⦌) :
    (simplexLeftFiberParameter f (f.app (Opposite.op ⦋n⦌) x)).app (Opposite.op ⦋n⦌)
      (fiberResolutionCanonicalSimplex f x) = SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := by
  rw [fiberResolutionCanonicalSimplex, ← SSet.yonedaEquiv_comp, simplexLeftFiberLift_parameter]

/-- 概要：元の単体 x からその恒等パラメーターの標準因子分解対象を作る。
方針：ラベル f(x) と標準左 fiber の単体を要素の圏に入れる。
規約：元の simplex category の次数 n を使う。使われ方：各 x の fiber の初期対象。 -/
def fiberResolutionCanonical {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    fiberResolutionCategory f n :=
  (fiberResolutionCoefficient f n).elementsMk
    (Opposite.op (Y.elementsMk (Opposite.op ⦋n⦌) (f.app (Opposite.op ⦋n⦌) x)))
      (fiberResolutionCanonicalSimplex f x)

/-- 概要：標準因子分解対象の augmentation の値は元の x。
方針：標準左 fiber の第一射影。
規約：元の n 単体の等号。使われ方：切断の端点。 -/
lemma fiberResolutionCanonical_value {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ} (x : X _⦋n⦌) :
    fiberResolutionValue f (fiberResolutionCanonical f x) = x :=
  fiberResolutionCanonicalSimplex_projection f x

/-- 概要：標準因子分解対象のパラメーターは恒等射。
方針：標準左 fiber の第二射影。
規約：元の n 単体の等号。使われ方：射の一意性の検証。 -/
lemma fiberResolutionCanonical_parameter {X Y : SSet.{u}} (f : X ⟶ Y) {n : ℕ}
    (x : X _⦋n⦌) : fiberResolutionParameter f (fiberResolutionCanonical f x) =
      SSet.yonedaEquiv (𝟙 (Δ[n] : SSet.{u})) := fiberResolutionCanonicalSimplex_parameter f x

end SerrePositivity.KST.SConstruction
