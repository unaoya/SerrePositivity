module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleNestedGenerators
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleLeibnizChains

/-!
# 任意の正規化鎖上の shuffle の入れ子結合則

概要：Berger–Fresse §1.1.3 の入れ子結合則を三つの任意の正規化鎖に対して示す。
方針：第三の入力の線形性と、第一・第二の入力の双線形性を順に使う。
規約：arity と正規化鎖の次数の移送を明示する。
使われ方：整数コチェイン複体上の部分合成の入れ子結合則へ移す。
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

/-- 概要：任意の正規化鎖に対して shuffle の部分合成は入れ子の結合則を満たす（Berger–Fresse §1.1.3）。
方針：正規化生成元上の有限和の等式を三つの入力に関する線形性で延長する。
規約：出力 arity と次数をそれぞれ加法の結合則で移送する。
使われ方：Barratt–Eccles オペラッドの複体の射の入れ子結合則を与える。 -/
lemma shuffleBilinear_nested_assoc (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1))
    (p q r : ℕ) (x : (normalizedChains A (m + 1)).X p)
    (y : (normalizedChains A (n + 1)).X q) (z : (normalizedChains A k).X r) :
    degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)
        ((normalizedChainMap A (simplicialArityMap (Nat.add_assoc m n k))).f (p + q + r)
          (shuffleBilinear A (m + n) k (nestedSlot m n i j) (p + q) r
            (shuffleBilinear A m (n + 1) i p q x y) z)) =
      shuffleBilinear A m (n + k) i p (q + r) x
        (shuffleBilinear A n k j q r y z) := by
  let F := (degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)).comp
    ((normalizedChainMap A (simplicialArityMap (Nat.add_assoc m n k))).f (p + q + r)).hom
  let B := shuffleBilinear A (m + n) k (nestedSlot m n i j) (p + q) r
  let C := shuffleBilinear A m (n + 1) i p q
  let D := shuffleBilinear A m (n + k) i p (q + r)
  let E := shuffleBilinear A n k j q r
  let L := C.compr₂ (F.comp (B.flip z))
  let R := D.compl₂ (E.flip z)
  have hLR : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) (n + 1) p q
    intro sx sy
    let f := F.comp (B (shuffleValue A m (n + 1) i p q sx sy))
    let g := (D (normalizedGenerator A (m + 1) p sx)).comp
      (E (normalizedGenerator A (n + 1) q sy))
    have hfg : ModuleCat.ofHom f = ModuleCat.ofHom g := by
      apply normalizedGenerator_hom_ext A k r
      intro sz
      change degreeTransport A (m + (n + k)) (Nat.add_assoc p q r)
          ((normalizedChainMap A (simplicialArityMap (Nat.add_assoc m n k))).f (p + q + r)
            (shuffleBilinear A (m + n) k (nestedSlot m n i j) (p + q) r
              (shuffleValue A m (n + 1) i p q sx sy) (normalizedGenerator A k r sz))) =
        shuffleBilinear A m (n + k) i p (q + r) (normalizedGenerator A (m + 1) p sx)
          (shuffleBilinear A n k j q r (normalizedGenerator A (n + 1) q sy)
            (normalizedGenerator A k r sz))
      rw [shuffleBilinear_generators]
      exact shuffleBilinear_nested_generators A m n k i j p q r sx sy sz
    change F (B (C (normalizedGenerator A (m + 1) p sx)
        (normalizedGenerator A (n + 1) q sy)) z) =
      D (normalizedGenerator A (m + 1) p sx) (E (normalizedGenerator A (n + 1) q sy) z)
    dsimp only [C]
    rw [shuffleBilinear_generators]
    exact congrArg (fun h => h z) hfg
  exact congrArg (fun h => h x y) hLR

end SerrePositivity.EInfinity.BarrattEccles
