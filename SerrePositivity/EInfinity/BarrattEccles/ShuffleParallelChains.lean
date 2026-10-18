module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleParallelGenerators
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
# 任意の正規化鎖上の shuffle の並列結合則

概要：Berger–Fresse §1.1.3 の異なる入力への二つの代入を任意の正規化鎖上で比較する。
方針：第三の入力の線形性と最初の二入力の双線形性で生成元の公式を延長する。
規約：入力次数 q,r の交換に (−1)^(qr) を掛け、arity と次数を移送する。
使われ方：Barratt–Eccles の複体の射の並列結合則へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：任意の正規化鎖上で並列合成は Koszul 符号を伴って可換である（Berger–Fresse §1.1.3）。
方針：各入力に関する線形写像の外延性で生成元の等式を延長する。
規約：代入位置は異なり、入力の arity と鎖次数は0を許す。
使われ方：オペラッドの parallel_assoc の公理を成分で検証する。 -/
lemma shuffleBilinear_parallel_assoc (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (p q r : ℕ) (x : (normalizedChains A (m + 2)).X p)
    (y : (normalizedChains A n).X q) (z : (normalizedChains A k).X r) :
    degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)
        ((normalizedChainMap A (simplicialArityMap (by omega : m + n + k = m + k + n))).f
          (p + q + r)
          (shuffleBilinear A (m + n) k (parallelSlot m n i j hji) (p + q) r
            ((normalizedChainMap A (simplicialArityMap
              (by omega : m + 1 + n = m + n + 1))).f (p + q)
              (shuffleBilinear A (m + 1) n i p q x y)) z)) =
      (-1 : ℤ) ^ (q * r) •
        shuffleBilinear A (m + k) n (parallelSlot m k j i hji.symm) (p + r) q
          ((normalizedChainMap A (simplicialArityMap
            (by omega : m + 1 + k = m + k + 1))).f (p + r)
            (shuffleBilinear A (m + 1) k j p r x z)) y := by
  let F := (degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)).comp
    ((normalizedChainMap A (simplicialArityMap (by omega : m + n + k = m + k + n))).f
      (p + q + r)).hom
  let H := ((normalizedChainMap A (simplicialArityMap
    (by omega : m + 1 + n = m + n + 1))).f (p + q)).hom
  let H' := ((normalizedChainMap A (simplicialArityMap
    (by omega : m + 1 + k = m + k + 1))).f (p + r)).hom
  let B := shuffleBilinear A (m + n) k (parallelSlot m n i j hji) (p + q) r
  let C := shuffleBilinear A (m + 1) n i p q
  let D := shuffleBilinear A (m + k) n (parallelSlot m k j i hji.symm) (p + r) q
  let E := shuffleBilinear A (m + 1) k j p r
  let L := C.compr₂ ((F.comp (B.flip z)).comp H)
  let R := (-1 : ℤ) ^ (q * r) • (D.comp (H'.comp (E.flip z)))
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 2) n p q
    intro sx sy
    let f := F.comp (B (H (shuffleValue A (m + 1) n i p q sx sy)))
    let g := (-1 : ℤ) ^ (q * r) •
      ((D.flip (normalizedGenerator A n q sy)).comp
        (H'.comp (E (normalizedGenerator A (m + 2) p sx))))
    have hfg : ModuleCat.ofHom f = ModuleCat.ofHom g := by
      apply normalizedGenerator_hom_ext A k r
      intro sz
      change degreeTransport A (m + k + n) (by omega : p + q + r = p + r + q)
          ((normalizedChainMap A (simplicialArityMap (by omega : m + n + k = m + k + n))).f
            (p + q + r)
            (shuffleBilinear A (m + n) k (parallelSlot m n i j hji) (p + q) r
              ((normalizedChainMap A (simplicialArityMap
                (by omega : m + 1 + n = m + n + 1))).f (p + q)
                (shuffleValue A (m + 1) n i p q sx sy)) (normalizedGenerator A k r sz))) =
        (-1 : ℤ) ^ (q * r) •
          shuffleBilinear A (m + k) n (parallelSlot m k j i hji.symm) (p + r) q
            ((normalizedChainMap A (simplicialArityMap
              (by omega : m + 1 + k = m + k + 1))).f (p + r)
              (shuffleBilinear A (m + 1) k j p r (normalizedGenerator A (m + 2) p sx)
                (normalizedGenerator A k r sz))) (normalizedGenerator A n q sy)
      rw [shuffleBilinear_generators]
      exact shuffleBilinear_parallel_generators A m n k i j hji p q r sx sy sz
    change F (B (H (C (normalizedGenerator A (m + 2) p sx)
        (normalizedGenerator A n q sy))) z) =
      (-1 : ℤ) ^ (q * r) • D (H' (E (normalizedGenerator A (m + 2) p sx) z))
        (normalizedGenerator A n q sy)
    dsimp only [C]
    rw [shuffleBilinear_generators]
    exact congrArg (fun h => h z) hfg
  exact congrArg (fun h => h x y) hLR

end SerrePositivity.EInfinity.BarrattEccles
