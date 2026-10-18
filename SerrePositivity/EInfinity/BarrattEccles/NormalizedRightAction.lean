module

public import SerrePositivity.EInfinity.BarrattEccles.NormalizedNaturality

/-!
# 次数同型を介した複体の右作用

概要：Berger–Fresse §1.1.2 の整数コチェイン右作用を正規化鎖の作用と比較する。
方針：次数同型の自然性を単体集合の右作用へ適用する。
規約：任意の鎖の元について成り立ち、基底元への制限を課さない。
使われ方：部分合成の射の等変性を正規化鎖上で検証する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 概要：複体の右作用の像を正規化鎖で評価する（Berger–Fresse §1.1.2）。
方針：単体集合の右作用について次数同型の自然性を使う。
規約：コチェイン次数は −q である。
使われ方：部分合成の入力への右作用を鎖次数へ移す。 -/
lemma complexRightAction_normalized_apply (n q : ℕ) (σ : Equiv.Perm (Fin n))
    (x : (complex A n).X (-(q : ℤ))) :
    (complexXIso A n q).hom ((complexRightAction A n σ).f (-(q : ℤ)) x) =
      (normalizedChainMap A (rightAction n σ)).f q ((complexXIso A n q).hom x) :=
  complexXIso_naturality_apply A (rightAction n σ) q x

/-- 概要：正規化鎖から戻した元への複体の右作用を計算する（Berger–Fresse §1.1.2）。
方針：単体集合の右作用について逆次数同型の自然性を使う。
規約：正規化鎖の次数は q である。
使われ方：部分合成の出力への右作用を鎖次数へ移す。 -/
lemma complexRightAction_normalized_inv_apply (n q : ℕ) (σ : Equiv.Perm (Fin n))
    (x : (normalizedChains A n).X q) :
    (complexRightAction A n σ).f (-(q : ℤ)) ((complexXIso A n q).inv x) =
      (complexXIso A n q).inv ((normalizedChainMap A (rightAction n σ)).f q x) :=
  complexXIso_inv_naturality_apply A (rightAction n σ) q x

end SerrePositivity.EInfinity.BarrattEccles
