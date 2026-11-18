module

public import SerrePositivity.EInfinity.BarrattEccles.NormalizedNaturality
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
# shuffle の対称群作用との等変性

概要：Berger–Fresse §0.10、§1.1.3 の shuffle 部分合成と内側・外側の置換作用を比較する。
方針：各頂点の置換合成の等変性を使い、正規化生成元の自然性と双線形性で拡張する。
規約：右作用は置換の右乗法であり、外側の作用では挿入位置も移る。
使われ方：Barratt–Eccles オペラッドの二種類の等変性を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：内側の置換への右作用は合成後の挿入区間への右作用である（Berger–Fresse §0.10）。
方針：shuffle 単体の各頂点で置換の部分合成の内側等変性を使う。
規約：shuffle 経路と外側の単体は変えない。
使われ方：正規化鎖上の部分合成の内側等変性を計算する。 -/
lemma shuffleSimplex_inner_rightAction (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (κ : Equiv.Perm (Fin n)) :
    shuffleSimplex m n i s x ((rightAction n κ).app _ y) =
      (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)).app _
        (shuffleSimplex m n i s x y) := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  simp only [simplexEquiv_shuffleSimplex, simplexEquiv_rightAction, permutationComposition_inner]

/-- 概要：外側の置換への右作用は挿入位置の移動と合成後の右作用である（Berger–Fresse §0.10）。
方針：shuffle 単体の各頂点で置換の部分合成の外側等変性を使う。
規約：右作用 ρ によって挿入位置 i は ρ(i) へ移る。
使われ方：正規化鎖上の部分合成の外側等変性を計算する。 -/
lemma shuffleSimplex_outer_rightAction (m n : ℕ) (i : Fin (m + 1)) {p q : ℕ}
    (s : ShufflePath p q) (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (ρ : Equiv.Perm (Fin (m + 1))) :
    shuffleSimplex m n i s ((rightAction (m + 1) ρ).app _ x) y =
      (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)).app _
        (shuffleSimplex m n (ρ i) s x y) := by
  apply (simplexEquiv (m + n) (p + q)).injective
  funext k
  simp only [simplexEquiv_shuffleSimplex, simplexEquiv_rightAction, permutationComposition_outer]

variable (A : Type u) [CommRing A]

/-- 概要：shuffle 和は内側の置換作用と可換する（Berger–Fresse §1.1.3）。
方針：各 shuffle 単体の等変性を使い、正規化鎖の射を和と符号へ分配する。
規約：符号は経路だけで決まり、置換作用で変化しない。
使われ方：生成元上の内側等変性を双線形写像へ拡張する。 -/
lemma shuffleValue_inner_rightAction (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (κ : Equiv.Perm (Fin n)) :
    shuffleValue A m n i p q x ((rightAction n κ).app _ y) =
      (normalizedChainMap A (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ))).f (p + q)
        (shuffleValue A m n i p q x y) := by
  classical
  simp only [shuffleValue, map_sum, map_zsmul, normalizedChainMap_generator,
    shuffleSimplex_inner_rightAction]

/-- 概要：shuffle 和は外側の置換作用と挿入位置の移動に関して等変である（Berger–Fresse §1.1.3）。
方針：各 shuffle 単体の外側等変性と正規化生成元の自然性を使う。
規約：作用後の単体の挿入位置は i、作用前は ρ(i) である。
使われ方：生成元上の外側等変性を双線形写像へ拡張する。 -/
lemma shuffleValue_outer_rightAction (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (x : (simplicial (m + 1)) _⦋p⦌) (y : (simplicial n) _⦋q⦌)
    (ρ : Equiv.Perm (Fin (m + 1))) :
    shuffleValue A m n i p q ((rightAction (m + 1) ρ).app _ x) y =
      (normalizedChainMap A (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ))).f (p + q)
        (shuffleValue A m n (ρ i) p q x y) := by
  classical
  simp only [shuffleValue, map_sum, map_zsmul, normalizedChainMap_generator,
    shuffleSimplex_outer_rightAction]

/-- 概要：任意の正規化鎖上の shuffle は内側の右作用に関して等変である（Berger–Fresse §1.1.3）。
方針：二つの双線形写像を正規化生成元上で比較する。
規約：内側の作用は出力の挿入区間へ延長する。
使われ方：整数コチェイン複体の部分合成の内側等変性へ移す。 -/
lemma shuffleBilinear_inner_rightAction (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (κ : Equiv.Perm (Fin n)) (x : (normalizedChains A (m + 1)).X p)
    (y : (normalizedChains A n).X q) :
    shuffleBilinear A m n i p q x ((normalizedChainMap A (rightAction n κ)).f q y) =
      (normalizedChainMap A (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ))).f (p + q)
        (shuffleBilinear A m n i p q x y) := by
  let L := (shuffleBilinear A m n i p q).compl₂ ((normalizedChainMap A (rightAction n κ)).f q).hom
  let R := (shuffleBilinear A m n i p q).compr₂
    ((normalizedChainMap A (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ))).f (p + q)).hom
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n p q
    intro sx sy
    simp only [L, R, LinearMap.compl₂_apply, LinearMap.compr₂_apply, normalizedChainMap_generator,
      shuffleBilinear_generators]
    exact shuffleValue_inner_rightAction A m n i p q sx sy κ
  exact congrArg (fun f => f x y) hLR

/-- 概要：任意の正規化鎖上の shuffle は外側の右作用に関して等変である（Berger–Fresse §1.1.3）。
方針：第一の入力への作用と出力への作用を双線形写像として生成元上で比較する。
規約：外側の置換に従って作用前の挿入位置を移す。
使われ方：整数コチェイン複体の部分合成の外側等変性へ移す。 -/
lemma shuffleBilinear_outer_rightAction (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (ρ : Equiv.Perm (Fin (m + 1))) (x : (normalizedChains A (m + 1)).X p)
    (y : (normalizedChains A n).X q) :
    shuffleBilinear A m n i p q ((normalizedChainMap A (rightAction (m + 1) ρ)).f p x) y =
      (normalizedChainMap A (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ))).f (p + q)
        (shuffleBilinear A m n (ρ i) p q x y) := by
  let L := (shuffleBilinear A m n i p q).comp
    ((normalizedChainMap A (rightAction (m + 1) ρ)).f p).hom
  let R := (shuffleBilinear A m n (ρ i) p q).compr₂
    ((normalizedChainMap A (rightAction (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ))).f (p + q)).hom
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) n p q
    intro sx sy
    simp only [L, R, LinearMap.comp_apply, LinearMap.compr₂_apply, normalizedChainMap_generator,
      shuffleBilinear_generators]
    exact shuffleValue_outer_rightAction A m n i p q sx sy ρ
  exact congrArg (fun f => f x y) hLR

end SerrePositivity.EInfinity.BarrattEccles
