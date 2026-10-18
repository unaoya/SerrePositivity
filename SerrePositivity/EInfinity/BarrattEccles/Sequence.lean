module

public import SerrePositivity.EInfinity.BarrattEccles.Normalized
public import SerrePositivity.Spectra.SymmetricSequence.Basic

/-!
# Barratt–Eccles の対称列

概要：Berger–Fresse §1.1 の EΣₙ と E(n) を有限全単射の骨格上の対称列にまとめる。
方針：右作用へ置換の逆元を代入して共変な左作用にする。
規約：Operad.rightAction の逆元の規約と一致させる。
使われ方：Barratt–Eccles オペラッドの sequence 成分を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory

/-- 概要：有限全単射に沿う EΣₙ の構造射（Berger–Fresse §1.1）。
方針：骨格の射の両端が等しいことを使い、逆置換の右作用を適用する。
規約：共変な構造射なので置換の逆元を使う。
使われ方：単体集合の対称列の射の部分となる。 -/
def simplicialSequenceMap {X Y : FiniteBijection} (f : X ⟶ Y) :
    simplicial (FiniteBijection.card X) ⟶ simplicial (FiniteBijection.card Y) := by
  obtain rfl := FiniteBijection.object_eq_of_hom f
  exact rightAction (FiniteBijection.card X) (FiniteBijection.equivOfHom f).symm

/-- 概要：自己全単射の構造射は逆置換の右作用である（Berger–Fresse §1.1）。
方針：骨格の対象の移送が恒等的であることを使う。
規約：任意の骨格対象の自己射について述べる。
使われ方：対称列の関手の法則と作用の規約を確認する。 -/
@[simp] lemma simplicialSequenceMap_self {X : FiniteBijection} (f : X ⟶ X) :
    simplicialSequenceMap f =
      rightAction (FiniteBijection.card X) (FiniteBijection.equivOfHom f).symm := by
  simp [simplicialSequenceMap]

/-- 概要：EΣₙ の単体集合の対称列（Berger–Fresse §1.1）。
方針：逆置換の右作用とその積の法則で関手を構成する。
規約：arity 0 を含む有限全単射の骨格上の関手。
使われ方：正規化鎖関手を合成して複体の対称列を得る。 -/
def simplicialSequence : SymmetricSequence SSet where
  obj X := simplicial (FiniteBijection.card X)
  map f := simplicialSequenceMap f
  map_id X := by
    simp only [simplicialSequenceMap_self, FiniteBijection.equivOfHom_id]
    exact rightAction_one _
  map_comp {X Y Z} f g := by
    obtain rfl := FiniteBijection.object_eq_of_hom f
    obtain rfl := FiniteBijection.object_eq_of_hom g
    simp only [simplicialSequenceMap_self, FiniteBijection.equivOfHom_comp]
    change rightAction _
        ((FiniteBijection.equivOfHom f).symm * (FiniteBijection.equivOfHom g).symm) = _
    exact rightAction_mul _ _ _

/-- 概要：正規化 Barratt–Eccles 複体の対称列（Berger–Fresse §1.1）。
方針：単体集合の対称列に正規化鎖関手を合成する。
規約：有限全単射の共変な作用を持つ整数コチェイン複体の列。
使われ方：Barratt–Eccles オペラッドの対称列となる。 -/
def sequence (A : Type u) [CommRing A] : SymmetricSequence (DifferentialGraded.Complex A) :=
  simplicialSequence ⋙ normalizedFunctor A

/-- 概要：対称列の第 n 成分は構成した E(n) である（Berger–Fresse §1.1）。
方針：関手の合成を標準 n 元対象で評価する。
規約：定義による等式である。
使われ方：対称列と arity ごとの構成を接続する。 -/
lemma sequence_level (A : Type u) [CommRing A] (n : ℕ) :
    SymmetricSequence.level (sequence A) n = complex A n := rfl

/-- 概要：対称列における置換の像は逆置換の右作用である（Berger–Fresse §1.1）。
方針：有限全単射から置換への対応を計算する。
規約：右作用に戻すには σ の逆元の像を取る。
使われ方：Operad.rightAction と既存の complexRightAction を同定する。 -/
lemma sequence_map_permutation (A : Type u) [CommRing A] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (sequence A).map (FiniteBijection.permutation n σ) = complexRightAction A n σ⁻¹ := by
  change (normalizedFunctor A).map (simplicialSequenceMap (FiniteBijection.permutation n σ)) = _
  rw [simplicialSequenceMap_self]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
