module

public import SerrePositivity.KST.Descent.InvariantExactness
public import Mathlib.LinearAlgebra.Prod

/-!
# 積の有理不変部分と指定比較

## 概要
二つの表現の積の不変部分を、不変部分の積と具体的に同定する。
各成分の不変部分の比較が同型なら、積の指定比較も同型になる。

## 方針
固定条件を二成分で評価し、同じ二成分を組み立てる逆写像を作る。

## 規約
通常の不変部分の主張。有限性・有理平均・hG の実構成はこの計算には不要。

## 使われ方
論文 定理 3.1 の軌道正方形で、(3.8) と中心上の帰納仮定を積の比較に組み合わせる。
-/

@[expose] public section

open Representation

namespace SerrePositivity.KST.Descent

variable {G M N M' N' : Type*} [Group G]
variable [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
variable [AddCommGroup M'] [Module ℚ M'] [AddCommGroup N'] [Module ℚ N']

/-- 概要：積の不変部分と不変部分の積との指定線形同型（論文 定理 3.1）。
方針：成分への射影と不変な二成分の組を互いの逆とする。
規約：無関係な抽象同型を選ばず、成分を変えない。
使われ方：軌道正方形の Mayer–Vietoris 列の積の項。 -/
noncomputable def invariantsProdEquiv (ρ : Representation ℚ G M) (σ : Representation ℚ G N) :
    (ρ.prod σ).invariants ≃ₗ[ℚ] ρ.invariants × σ.invariants where
  toFun x := (⟨x.val.1, fun g ↦ congrArg Prod.fst (x.property g)⟩,
    ⟨x.val.2, fun g ↦ congrArg Prod.snd (x.property g)⟩)
  invFun x := ⟨(x.1.val, x.2.val), fun g ↦ Prod.ext (x.1.property g) (x.2.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ρ : Representation ℚ G M} {σ : Representation ℚ G N}
variable {ρ' : Representation ℚ G M'} {σ' : Representation ℚ G N'}

/-- 概要：二つの指定同変写像から積の同変写像を作る（論文 定理 3.1）。
方針：線形写像の積を取り、同変性を二成分で証明する。
規約：各成分の同型性は構成には不要。
使われ方：(3.8) と中心上の比較を同じ積の写像として組み立てる。 -/
def productIntertwiningMap (f : IntertwiningMap ρ ρ') (g : IntertwiningMap σ σ') :
    IntertwiningMap (ρ.prod σ) (ρ'.prod σ') where
  toLinearMap := f.toLinearMap.prodMap g.toLinearMap
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (f (ρ h x.1), g (σ h x.2)) = (ρ' h (f x.1), σ' h (g x.2))
    apply Prod.ext
    · exact LinearMap.congr_fun (f.isIntertwining' h) x.1
    · exact LinearMap.congr_fun (g.isIntertwining' h) x.2

/-- 概要：積の不変部分の同定は指定比較と可換（論文 定理 3.1）。
方針：両辺が各成分で f と g を評価することを確認する。
規約：不変性の証明項は成分の値を変えない。
使われ方：Mayer–Vietoris 比較の積の項と五項補題の接続。 -/
theorem invariantsProdEquiv_naturality (f : IntertwiningMap ρ ρ') (g : IntertwiningMap σ σ')
    (x : (ρ.prod σ).invariants) :
    invariantsProdEquiv ρ' σ' (invariantMap (productIntertwiningMap f g) x) =
      (invariantMap f (invariantsProdEquiv ρ σ x).1,
        invariantMap g (invariantsProdEquiv ρ σ x).2) := rfl

/-- 概要：成分の不変部分の比較が同型なら積の不変部分の比較も同型（論文 定理 3.1）。
方針：積の不変部分を成分へ分け、成分ごとの単射性と全射性を適用する。
規約：f、g 自体の同型性は要求せず、不変部分の比較の同型性だけを使う。
使われ方：(3.8) と中心上の帰納仮定から軌道正方形の積の辺を同型とする。 -/
theorem invariantMap_product_bijective (f : IntertwiningMap ρ ρ') (g : IntertwiningMap σ σ')
    (hf : Function.Bijective (invariantMap f)) (hg : Function.Bijective (invariantMap g)) :
    Function.Bijective (invariantMap (productIntertwiningMap f g)) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply Prod.ext
    · have h₁ : invariantMap f (invariantsProdEquiv ρ σ x).1 =
          invariantMap f (invariantsProdEquiv ρ σ y).1 := by
        simpa only [invariantsProdEquiv_naturality] using
          congrArg (fun z ↦ (invariantsProdEquiv ρ' σ' z).1) h
      exact congrArg Subtype.val (hf.1 h₁)
    · have h₂ : invariantMap g (invariantsProdEquiv ρ σ x).2 =
          invariantMap g (invariantsProdEquiv ρ σ y).2 := by
        simpa only [invariantsProdEquiv_naturality] using
          congrArg (fun z ↦ (invariantsProdEquiv ρ' σ' z).2) h
      exact congrArg Subtype.val (hg.1 h₂)
  · intro y
    obtain ⟨x₁, hx₁⟩ := hf.2 (invariantsProdEquiv ρ' σ' y).1
    obtain ⟨x₂, hx₂⟩ := hg.2 (invariantsProdEquiv ρ' σ' y).2
    refine ⟨(invariantsProdEquiv ρ σ).symm (x₁, x₂), ?_⟩
    apply (invariantsProdEquiv ρ' σ').injective
    exact Prod.ext hx₁ hx₂

end SerrePositivity.KST.Descent
