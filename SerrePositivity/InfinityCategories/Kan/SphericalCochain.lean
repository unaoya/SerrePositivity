module

public import SerrePositivity.InfinityCategories.Kan.SphericalBoundaryMap
public import SerrePositivity.InfinityCategories.Kan.NormalizedValueCochains

/-!
概要：低次元で定数の単体的な射から高次群係数の正規化 cocycle を得る。
方針：各単体の像を境界定数単体として読み、球面的境界の交代関係を適用する。
規約：cochain の次数は n + 2。幾何的な塔の微分との同定はまだ主張しない。
使われ方：Goerss–Jardine I §7、III §2、VIII §1。実際の射と交代 cochain の最初の比較。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphericalCochain

noncomputable section

variable {K X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌} (f : K ⟶ X)
  (h : ∀ s : K _⦋n + 1⦌, yonedaEquiv.symm s ≫ f = SSet.const x)

/-- 概要：低次元で定数の射の単体の像は境界定数単体。
方針：各境界面へ制限して低次元の定数条件を使う。
規約：Kan 性はこの代表の構成に不要。
使われ方：Goerss–Jardine I §7。実際の射の高次群係数。 -/
def simplexValue (s : K _⦋n + 2⦌) : X.PtSimplex (n + 2) x where
  map := yonedaEquiv.symm s ≫ f
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm, h]

/-- 概要：退化単体の像の代表は定数単体。
方針：退化と Yoneda の自然性により一つ低い単体の定数像へ戻す。
規約：代表そのものの等式であり、商だけの等式ではない。
使われ方：Goerss–Jardine III §2。正規化 cochain の退化での零性。 -/
theorem simplexValue_degeneracy (s : K _⦋n + 1⦌) (i : Fin (n + 2)) :
    simplexValue f h (K.σ i s) = .const := by
  apply RelativeMorphism.ext
  change yonedaEquiv.symm (K.σ i s) ≫ f = SSet.const x
  rw [← stdSimplex.σ_comp_yonedaEquiv_symm, Category.assoc, h, comp_const]

/-- 概要：一つ高い単体の像は各面の像を持つ球面的境界。
方針：面と Yoneda の自然性で各面の代表を比較する。
規約：元の単体の実際の像を使う。
使われ方：Goerss–Jardine I §7、VIII §1。交代 cocycle 関係。 -/
def boundary (s : K _⦋n + 3⦌) :
    SphericalBoundary (fun j ↦ simplexValue f h (K.δ j s)) where
  map := yonedaEquiv.symm s ≫ f
  face_eq j := by
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
    rfl

variable [KanComplex X]

/-- 概要：低次元で定数の射から非退化単体上の高次群係数を取る。
方針：各単体の像の境界定数な代表を加法的ホモトピー類へ送る。
規約：係数は実際の次数 n + 2 のホモトピー群。
使われ方：Goerss–Jardine III §2、VIII §1。実際の幾何から得る正規化 cochain。 -/
def cochain : K.nonDegenerate (n + 2) → Additive (KanHomotopyGroup X (n + 1) x) :=
  fun s ↦ SphericalBoundary.additiveClass (simplexValue f h s.val)

/-- 概要：正規化 cochain を退化で零に延長すると全単体の像の類に一致する。
方針：非退化なら定義、退化なら一つの退化写像からの表示と定数像を使う。
規約：任意の単体についての式。
使われ方：Goerss–Jardine III §2、VIII §1。正規化微分の各面の計算。 -/
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

/-- 概要：低次元で定数の射の高次群係数は通常の正規化 cocycle である。
方針：正規化の交代微分を各面の像の類へ直し、球面的境界関係を適用する。
規約：塔の連結準同型の計算を仮定せず、実際の射の像を計算する。
使われ方：Goerss–Jardine I §7、III §2、VIII §1。幾何的な係数の cocycle 条件。 -/
theorem differential_cochain :
    NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (KanHomotopyGroup X (n + 1) x))) (n + 2)
      (cochain f h) = 0 := by
  funext s
  rw [NormalizedValueCochains.differential_apply]
  simp only [zeroExtend_cochain]
  exact SphericalBoundary.alternatingClass_eq_zero (boundary f h s.val)

end

end SerrePositivity.KST.Spectra.SphericalCochain
