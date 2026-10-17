module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Polynomial.Expand

/-!
# André E1：通常のモニック根添加の自由性

## 概要

正次数のモニック多項式の通常根添加環は自由かつ忠実平坦である。
有限段の変数置換 `Y = Z^n` と関係式の冪にも同じ結論を与える。
BS 著者版 Thm 7.14（p.61）、Rem 7.15(1)（p.62）の通常代数の準備である。

## 方針

Mathlib のモニック剰余の冪基底を使う。非零係数環では正次数から係数射の単射性を得て、
自由加群の忠実平坦性を適用する。零係数環は加群の自明性で処理する。
原典の Prop 7.11 を使う証明とは異なる経路の準備で、pd 包との同定は含まない。

## 規約

正次数を明示する。`1` はモニックだが根添加環が零となり、非零の係数環上忠実平坦でない。
自由性だけから perfectoid 性や完備化後の忠実平坦性を推論しない。

## 使われ方

`R/ϖ[Y^(1/p^∞)]/(f^p)` の有限段に必要なモニック商の計算に使う。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

open Polynomial

/-- 概要：正次数モニックの根添加環は係数環上忠実平坦。
方針：モニック剰余の自由性と係数射の単射性を使い、零環は別に処理する。
規約：次数の仮定は定数 `1` を除外する。
使われ方：BS Rem 7.15（著者版 p.62）のモニック商の有限段の準備。 -/
theorem adjoinRoot_faithfullyFlat {R : Type u} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (AdjoinRoot f) := by
  let := hf.free_adjoinRoot
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    let : Nontrivial (AdjoinRoot f) :=
      (AdjoinRoot.of.injective_of_monic_of_degree_pos hf
        (natDegree_pos_iff_degree_pos.mp hdeg)).nontrivial
    infer_instance

/-- 概要：正次数モニックに根を添加した通常の自由忠実平坦拡大が存在する。
方針：`AdjoinRoot f` とその標準根を取る。
規約：完備性・perfectoid 性は結論に含まない。
使われ方：BS Thm 7.14（著者版 p.61）の一段の通常代数部分。 -/
theorem exists_monicRootedFaithfullyFlat {R : Type u} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (r : T),
      (letI := φ.toAlgebra; Module.Free R T ∧ Module.FaithfullyFlat R T) ∧
      f.eval₂ φ r = 0 := by
  refine ⟨AdjoinRoot f, inferInstance, algebraMap R (AdjoinRoot f),
    AdjoinRoot.root f, ?_, ?_⟩
  · rw [toAlgebra_algebraMap]
    exact ⟨hf.free_adjoinRoot, adjoinRoot_faithfullyFlat f hf hdeg⟩
  · exact AdjoinRoot.eval₂_root f

/-- 概要：モニック f の変数を n 乗に置換した後の m 乗関係式も、自由忠実平坦な商を与える。
方針：expand と冪のモニック性・次数公式を通常根添加の結果に適用する。
規約：`n,m` は正であり、有限段の商だけを扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の `P/(f^p)` の有限段。 -/
theorem expandedPower_quotient_free_faithfullyFlat {R : Type u} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Module.Free R (AdjoinRoot ((expand R n f) ^ m)) ∧
      Module.FaithfullyFlat R (AdjoinRoot ((expand R n f) ^ m)) := by
  have he : (expand R n f).Monic := hf.expand hn
  have hd : 0 < ((expand R n f) ^ m).natDegree := by
    rw [he.natDegree_pow, natDegree_expand]
    exact Nat.mul_pos hm (Nat.mul_pos hdeg hn)
  exact ⟨(he.pow m).free_adjoinRoot,
    adjoinRoot_faithfullyFlat _ (he.pow m) hd⟩

end SerrePositivity.BhattScholze.Andre
