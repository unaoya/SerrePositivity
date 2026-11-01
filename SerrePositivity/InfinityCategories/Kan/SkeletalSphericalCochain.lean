module

public import SerrePositivity.InfinityCategories.Kan.SphericalCochain
public import SerrePositivity.InfinityCategories.Kan.SkeletalAttachmentPushout

/-!
概要：骨格上で低次元を定数に送る射のセルごとの延長障害。
方針：骨格の単体の持ち上げから正規化 cochain を作り、各セルの境界充填を交代微分で判定する。
規約：Mathlib の skeleton d は次元 d 未満。射は通常の n+2 骨格上にある。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な延長障害と交代微分の比較。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalSphericalCochain

noncomputable section

variable {K X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
  (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ X)
  (h : ∀ s : (K.skeleton (n + 3) : SSet.{u}) _⦋n + 1⦌,
    yonedaEquiv.symm s ≫ f = SSet.const x)

/-- 概要：骨格上の射の単体の像を境界定数単体へ送る。
方針：骨格に必ず属する単体を持ち上げ、低次元で定数の射の像を使う。
規約：単体の実際の次元は n + 2。
使われ方：Goerss–Jardine I §7、VIII §1。セルの境界上の係数。 -/
def simplexValue (s : K _⦋n + 2⦌) : X.PtSimplex (n + 2) x :=
  SphericalCochain.simplexValue f h ⟨s, K.mem_skeleton s⟩

/-- 概要：骨格上の射の退化単体の像の代表は定数。
方針：骨格の単体の持ち上げは退化と可換なので、全体の射の退化計算を使う。
規約：代表単体そのものの等式。
使われ方：Goerss–Jardine III §2、VIII §1。正規化された係数の零性。 -/
theorem simplexValue_degeneracy (s : K _⦋n + 1⦌) (i : Fin (n + 2)) :
    simplexValue f h (K.σ i s) = .const :=
  SphericalCochain.simplexValue_degeneracy f h ⟨s, K.mem_skeleton s⟩ i

variable [KanComplex X]

/-- 概要：骨格上の射の非退化単体ごとのホモトピー類。
方針：像の境界定数単体を高次の可換ホモトピー群へ送る。
規約：cochain の次数と係数の実際の次数はともに n + 2。
使われ方：Goerss–Jardine VIII §1。セルの延長障害の入力。 -/
def cochain : K.nonDegenerate (n + 2) → Additive (KanHomotopyGroup X (n + 1) x) :=
  fun s ↦ SphericalBoundary.additiveClass (simplexValue f h s.val)

/-- 概要：骨格の係数を零延長すると任意の単体の像の類になる。
方針：退化単体を一つの退化として表し、その像が定数であることを使う。
規約：正規化 cochain の零延長。
使われ方：Goerss–Jardine III §2、VIII §1。セル境界の全ての面の寄与。 -/
theorem zeroExtend_cochain (s : K _⦋n + 2⦌) :
    NormalizedValueCochains.zeroExtend K
      (AddCommGrpCat.of (Additive (KanHomotopyGroup X (n + 1) x))) (n + 2)
      (cochain f h) s = SphericalBoundary.additiveClass (simplexValue f h s) := by
  classical
  unfold NormalizedValueCochains.zeroExtend
  split_ifs with hs
  · rfl
  · have hd : s ∈ K.degenerate (n + 2) := (K.mem_degenerate_iff_notMem_nonDegenerate s).2 hs
    rw [K.degenerate_eq_iUnion_range_σ] at hd
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hd
    rw [simplexValue_degeneracy, SphericalBoundary.additiveClass_const]

/-- 概要：骨格上の射の次のセルへの延長障害は通常の交代微分。
方針：各面の値への零延長の式を正規化微分へ適用する。
規約：セルは非退化な n+3 単体。
使われ方：Goerss–Jardine VIII §1。幾何的な境界の交代和との厳密な式。 -/
theorem differential_cochain_apply (s : K.nonDegenerate (n + 3)) :
    NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (KanHomotopyGroup X (n + 1) x))) (n + 2)
      (cochain f h) s =
        SphericalBoundary.alternatingClass (fun j ↦ simplexValue f h (K.δ j s.val)) := by
  rw [NormalizedValueCochains.differential_apply]
  simp only [zeroExtend_cochain]
  rfl

/-- 概要：骨格上の射の一つの新規セルの境界は微分が零のとき丁度充填できる。
方針：球面的境界の充填判定を、そのセルの全ての面の像へ適用する。
規約：境界射は指定した面族の実際の貼り合わせ。
使われ方：Goerss–Jardine I §7、VIII §1。幾何的な延長障害のセルごとの判定。 -/
theorem cell_filler_iff (s : K.nonDegenerate (n + 3)) :
    (∃ φ : (Δ[n + 3] : SSet.{u}) ⟶ X,
      (boundary (n + 3)).ι ≫ φ =
        SphericalBoundary.boundaryMap (fun j ↦ simplexValue f h (K.δ j s.val))) ↔
      NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (KanHomotopyGroup X (n + 1) x))) (n + 2)
        (cochain f h) s = 0 := by
  rw [differential_cochain_apply]
  exact SphericalBoundary.boundary_filler_iff _

end

end SerrePositivity.KST.Spectra.SkeletalSphericalCochain
