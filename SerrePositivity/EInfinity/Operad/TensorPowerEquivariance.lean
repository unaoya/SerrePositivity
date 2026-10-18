module

public import SerrePositivity.CategoryTheory.Monoidal.PowerBijectionFunctor
public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerBlockPermutations

/-!
# 標準有限集合の全単射がテンソル冪に誘導する射

概要：Berger–Moerdijk §1 の入力ブロックの交換を、有限全単射のテンソル冪への作用として扱う。
方針：既存の有限全単射上の関手を使い、連結と独立な二つの全単射の両立を証明する。
規約：始域と終域の長さは同じ自然数の異なる式でよい。
使われ方：Schur 演算の外側等変性でブロック交換を入力のテンソル冪へ運ぶ。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：標準有限集合の全単射が誘導するテンソル冪の射（Berger–Moerdijk §1）。
方針：既存の有限全単射の関手を標準有限集合の間の射で評価する。
規約：係数の移送を含む既存の置換作用を使う。
使われ方：長さの式が異なる入力ブロックの交換を記述する。 -/
def tensorPowerEquivMap (X : C) {m n : ℕ} (e : Fin m ≃ Fin n) : power X m ⟶ power X n :=
  (bijectionFunctor X).map
    (FiniteBijection.homOfEquiv (X := FiniteBijection.of m) (Y := FiniteBijection.of n) e)

/-- 概要：恒等全単射はテンソル冪の恒等射を誘導する（Berger–Moerdijk §1）。
方針：有限全単射の関手の恒等射則を使う。
規約：arity は任意の自然数。
使われ方：空のブロックや再帰の基底で置換作用を簡約する。 -/
@[simp]
lemma tensorPowerEquivMap_refl (X : C) (n : ℕ) :
    tensorPowerEquivMap X (Equiv.refl (Fin n)) = 𝟙 (power X n) := by
  exact (congrArg (fun f : FiniteBijection.of n ⟶ FiniteBijection.of n =>
    (bijectionFunctor X).map f) (FiniteBijection.homOfEquiv_refl (FiniteBijection.of n))).trans
      ((bijectionFunctor X).map_id (FiniteBijection.of n))

/-- 概要：全単射の合成はテンソル冪の射の合成になる（Berger–Moerdijk §1）。
方針：有限全単射の合成則と関手の合成則を使う。
規約：左の全単射を先に適用する `Equiv.trans` の向きで述べる。
使われ方：ブロック交換を小さい入力交換へ分解して計算する。 -/
lemma tensorPowerEquivMap_trans (X : C) {l m n : ℕ} (e : Fin l ≃ Fin m) (f : Fin m ≃ Fin n) :
    tensorPowerEquivMap X (e.trans f) = tensorPowerEquivMap X e ≫ tensorPowerEquivMap X f := by
  exact (congrArg (fun g : FiniteBijection.of l ⟶ FiniteBijection.of n =>
    (bijectionFunctor X).map g)
    (FiniteBijection.homOfEquiv_trans (X := FiniteBijection.of l) (Y := FiniteBijection.of m)
      (Z := FiniteBijection.of n) e f)).trans
        ((bijectionFunctor X).map_comp
          (FiniteBijection.homOfEquiv (X := FiniteBijection.of l) (Y := FiniteBijection.of m) e)
          (FiniteBijection.homOfEquiv (X := FiniteBijection.of m) (Y := FiniteBijection.of n) f))

/-- 概要：長さの等式による標準全単射はテンソル冪の等式の射を誘導する（Berger–Moerdijk §1）。
方針：長さの等式で同一視し、恒等全単射の場合へ帰着する。
規約：等しい長さの異なる式の比較に使う。
使われ方：入力の連結の括弧付けの移送を計算する。 -/
@[simp]
lemma tensorPowerEquivMap_finCongr (X : C) {m n : ℕ} (h : m = n) :
    tensorPowerEquivMap X (finCongr h) = eqToHom (congrArg (power X) h) := by
  subst n
  exact tensorPowerEquivMap_refl X m

/-- 概要：同じ長さの全単射の誘導射は既存の対称群作用である（Berger–Moerdijk §1）。
方針：標準置換に対する既存の有限全単射の関手の式を使う。
規約：入力には Koszul 符号を含む。
使われ方：独立なブロック内の置換と連結の両立を使う。 -/
lemma tensorPowerEquivMap_perm (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    tensorPowerEquivMap X σ = (permutationAction X n σ).asIso.hom :=
  bijectionFunctor_map_permutation X n σ

/-- 概要：テンソル冪の連結は二つの独立な全単射と両立する（Berger–Moerdijk §1）。
方針：全単射で長さが等しいことを使い、既存のブロック置換の等変性へ帰着する。
規約：始域と終域の長さの式は異なってよい。
使われ方：大きなブロック交換を小さいブロックの交換へ分解する。 -/
@[reassoc] lemma appendIso_equivariance (X : C) {a a' b b' : ℕ}
    (e : Fin a ≃ Fin a') (f : Fin b ≃ Fin b') :
    (tensorPowerEquivMap X e ⊗ₘ tensorPowerEquivMap X f) ≫ (appendIso X a' b').hom =
      (appendIso X a b).hom ≫ tensorPowerEquivMap X (FiniteBijection.blockEquiv e f) := by
  have ha : a = a' := Fin.equiv_iff_eq.mp ⟨e⟩
  have hb : b = b' := Fin.equiv_iff_eq.mp ⟨f⟩
  subst a'
  subst b'
  simp only [tensorPowerEquivMap_perm]
  exact appendIso_block_permutation X a b e f

end SerrePositivity.EInfinity
