module

public import SerrePositivity.KST.Spectra.SimplexLastContraction

/-!
概要：最後のホーンの最後の頂点への収縮。
方針：標準単体の明示的な収縮をホーンへ制限し、包含で二つの端点を検出する。
規約：ホーンの次元は n+1。零次元の空なホーンは含まない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2。境界の正規化。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.LastHornContraction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：最後のホーンの最後の頂点。
方針：標準単体の最後の頂点は零番目の頂点を欠くことを使う。
規約：次元 n+1 は正。
使われ方：Goerss–Jardine I §7。収縮の定数値。 -/
def vertex (n : ℕ) : (horn.{u} (n + 1) (Fin.last (n + 1))) _⦋0⦌ :=
  ⟨SimplexLastContraction.vertex (n + 1), by
    rw [mem_horn_iff_notMem_range]
    refine ⟨0, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp at this
    · rintro ⟨i, hi⟩
      change Fin.last (n + 1) = 0 at hi
      have := congrArg Fin.val hi
      simp at this⟩

/-- 概要：最後のホーン上に制限した収縮写像。
方針：各次数の収縮後の単体がホーンを保つことを使う。
規約：標準単体への包含と厳密に可換。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2。境界のホーン上での収縮。 -/
def map (n : ℕ) :
    (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶
      (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u}) where
  app m := ↾(fun p : ((horn.{u} (n + 1) (Fin.last (n + 1))).obj m × (Δ[1] : SSet.{u}).obj m) ↦
    ⟨SimplexLastContraction.simplex p.1.val p.2,
      SimplexLastContraction.simplex_mem_horn p.1.val p.1.property p.2⟩)
  naturality m m' f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply stdSimplex.ext
    intro i
    rfl

/-- 概要：ホーンの収縮を含めると標準単体の収縮に一致。
方針：制限写像の定義を比較する。
規約：区間との積では包含を第一成分へ作用させる。
使われ方：Goerss–Jardine I §7。端点と基点の比較。 -/
@[reassoc]
theorem map_ι (n : ℕ) : map.{u} n ≫ (horn (n + 1) (Fin.last (n + 1))).ι =
    (horn (n + 1) (Fin.last (n + 1))).ι ▷ (Δ[1] : SSet.{u}) ≫
      SimplexLastContraction.map (n + 1) := rfl

/-- 概要：ホーンの収縮の始点は恒等射。
方針：包含の単射性と標準単体の端点の計算で示す。
規約：ホーン上の射の厳密な等式。
使われ方：Goerss–Jardine I §7。境界の正規化の初期値。 -/
@[reassoc (attr := simp)]
theorem zero (n : ℕ) : SSet.ι₀ ≫ map.{u} n = 𝟙 _ := by
  apply (cancel_mono (horn (n + 1) (Fin.last (n + 1))).ι).1
  rw [Category.assoc, map_ι, ← Category.assoc, SSet.ι₀_comp, Category.assoc,
    SimplexLastContraction.zero, Category.comp_id, Category.id_comp]

/-- 概要：ホーンの収縮の終点は最後の頂点に定数。
方針：包含へ合成して標準単体の終点の計算へ移す。
規約：非空なホーンの定数射。
使われ方：Goerss–Jardine I §7。正規化後のホーンの境界条件。 -/
@[reassoc (attr := simp)]
theorem one (n : ℕ) : SSet.ι₁ ≫ map.{u} n = SSet.const (vertex n) := by
  apply (cancel_mono (horn (n + 1) (Fin.last (n + 1))).ι).1
  rw [Category.assoc, map_ι, ← Category.assoc, SSet.ι₁_comp, Category.assoc,
    SimplexLastContraction.one, SSet.comp_const, SSet.const_comp]
  rfl

/-- 概要：最後のホーンの恒等射から最後の頂点の定数射へのホモトピー。
方針：制限した収縮写像と端点の式を束ねる。
規約：実際の区間ホモトピー。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2。境界の充填判定の幾何的入力。 -/
def homotopy (n : ℕ) : SSet.Homotopy
    (𝟙 (horn.{u} (n + 1) (Fin.last (n + 1)) : SSet.{u})) (SSet.const (vertex n)) where
  h := map n
  h₀ := zero n
  h₁ := one n
  rel := by ext m ⟨⟨x, hx⟩, t⟩; exact hx.elim

end

end SerrePositivity.KST.Spectra.LastHornContraction
