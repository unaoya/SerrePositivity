module

public import SerrePositivity.EInfinity.BarrattEccles.Nondegenerate
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# EΣₙ の追加退化

概要：Berger–Fresse §1.1 の EΣₙ の収縮を単位頂点の追加で構成する。
方針：置換列の先頭に単位置換を付け、追加退化の全ての恒等式を確認する。
規約：一点への augmentation を用い、収縮には群同変性を要求しない。
使われ方：正規化鎖の augmentation が鎖ホモトピー同値であることを導く。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：EΣₙ の単体の先頭に単位置換を付ける（Berger–Fresse §1.1）。
方針：置換列の同値に沿って Fin.cons を使う。
規約：単体次数を一つ増やす写像である。
使われ方：追加退化の成分となる。 -/
def prependIdentity (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    (simplicial n) _⦋q + 1⦌ :=
  (simplexEquiv n (q + 1)).symm (Fin.cons 1 (simplexEquiv n q x))

/-- 概要：先頭への単位追加の頂点列（Berger–Fresse §1.1）。
方針：置換列の同値と逆写像を消去する。
規約：Fin.cons の先頭が単位置換である。
使われ方：追加退化の恒等式を頂点ごとに確認する。 -/
@[simp] lemma simplexEquiv_prependIdentity (n q : ℕ) (x : (simplicial n) _⦋q⦌) :
    simplexEquiv n (q + 1) (prependIdentity n q x) =
      Fin.cons 1 (simplexEquiv n q x) :=
  (simplexEquiv n (q + 1)).apply_symm_apply _

/-- 概要：EΣₙ の一点への augmentation（Berger–Fresse §1.1）。
方針：各次数で一点への一意な写像を取る。
規約：augmentation の値は PUnit。
使われ方：自由加群化すると A への augmentation を与える。 -/
def augmented (n : ℕ) : SimplicialObject.Augmented (Type) where
  left := simplicial n
  right := PUnit
  hom := { app _ := ↾fun _ => PUnit.unit }

/-- 概要：EΣₙ の単位頂点を用いた追加退化（Berger–Fresse §1.1）。
方針：先頭への単位追加が面写像と退化写像について満たす恒等式を頂点で証明する。
規約：追加退化は augmentation の一点に単位の 0 単体を対応させる。
使われ方：EΣₙ の可縮性およびその線形化の鎖収縮を与える。 -/
def extraDegeneracy (n : ℕ) : SimplicialObject.Augmented.ExtraDegeneracy (augmented n) where
  s' := ↾fun _ => (simplexEquiv n 0).symm (fun _ => 1)
  s q := ↾(prependIdentity n q)
  s'_comp_ε := by ext x; rfl
  s₀_comp_δ₁ := by
    ext x
    change (simplicial n).δ 1 (prependIdentity n 0 x) =
      (simplexEquiv n 0).symm (fun _ => 1)
    apply (simplexEquiv n 0).injective
    funext j
    fin_cases j
    simp
  s_comp_δ₀ q := by
    ext x
    change (simplicial n).δ 0 (prependIdentity n q x) = x
    apply (simplexEquiv n q).injective
    funext j
    simp
  s_comp_δ q i := by
    ext x
    change (simplicial n).δ i.succ (prependIdentity n (q + 1) x) =
      prependIdentity n q ((simplicial n).δ i x)
    apply (simplexEquiv n (q + 1)).injective
    funext j
    simp only [simplexEquiv_δ, simplexEquiv_prependIdentity]
    cases j using Fin.cases <;> simp
  s_comp_σ q i := by
    ext x
    change (simplicial n).σ i.succ (prependIdentity n q x) =
      prependIdentity n (q + 1) ((simplicial n).σ i x)
    apply (simplexEquiv n (q + 2)).injective
    funext j
    simp only [simplexEquiv_σ, simplexEquiv_prependIdentity]
    cases j using Fin.cases <;> simp

end SerrePositivity.EInfinity.BarrattEccles
