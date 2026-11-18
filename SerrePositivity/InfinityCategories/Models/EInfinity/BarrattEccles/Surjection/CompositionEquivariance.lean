module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NormalizedAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompositionAll
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Surjectivity
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEquivariance

/-!
模型。文献の定義との比較は後で
# 全射語の部分合成の内外置換同変性

概要：Berger–Fresse §1.2.4・§1.3.6 の部分合成の対称群同変性を証明する。
方針：二入力を全射 TR で持ち上げ、BE の右作用の同変性を値の逆置換作用へ送る。
規約：置換と挿入位置は既存 BE のラベルの規約を継承する。
使われ方：χ の対称 dg オペラッドの内外同変性の成分公式。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：内側の値の逆置換は出力の挿入区間の逆置換へ移る（BF §1.2.4・§1.3.6）。
方針：全射 TR の二つの逆像で BE の内側右作用同変性を評価する。
規約：全 arity・全次数。空の内側区間も含む。
使われ方：χ の inner_equivariance の成分計算。 -/
lemma partialComposition_inner_rightAction (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (κ : Equiv.Perm (Fin n)) (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) p) (y : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p q i x (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A κ⁻¹ y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)⁻¹ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p q i x y) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A (m + 1) p x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n q y
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (p + q))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_inner_rightAction A m n i p q κ x y)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_rightAction] using h

/-- 概要：外側の値の逆置換は挿入位置を移し出力の逆置換へ移る（BF §1.2.4・§1.3.6）。
方針：全射 TR の二つの逆像で BE の外側右作用同変性を評価する。
規約：作用前の挿入位置は ρ(i)、作用後は i とする。
使われ方：χ の outer_equivariance の成分計算。 -/
lemma partialComposition_outer_rightAction (m n : ℕ) (i : Fin (m + 1)) (p q : ℕ)
    (ρ : Equiv.Perm (Fin (m + 1))) (x : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 1) p) (y : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p q i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A ρ⁻¹ x) y =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.renameLinear A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)⁻¹
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m n p q (ρ i) x y) := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A (m + 1) p x
  obtain ⟨y, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_surjective A n q y
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + n) (p + q))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.shuffleBilinear_outer_rightAction A m n i p q ρ x y)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffleBilinear, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_rightAction] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
