module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Schur
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Slots
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Insertion

/-!
模型。文献の定義との比較は後で
# 複体上の対称オペラッド

概要：Berger–Moerdijk §1 の対称オペラッドを、各入力への部分合成で定義する。
方針：対称列を再利用し、内側・外側の等変性と入れ子・独立な合成の結合則を記録する。
規約：arity 0 を含む。複体のテンソルは既存の Koszul 対称モノイダル構造。
使われ方：Barratt–Eccles オペラッドとその代数を定義する共通の型となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

/-- 概要：非有界複体上の対称オペラッド（Berger–Moerdijk §1）。
方針：各 arity の複体と対称群作用を既存の対称列で持ち、部分合成を chain map で与える。
規約：二種類の等変性、入れ子・独立な合成の結合則、左右の単位則を要求する。
使われ方：自由代数と Barratt–Eccles の代数の構成の入力となる。 -/
structure Operad (A : Type u) [CommRing A] where
  /-- 概要：各 arity の複体と対称群作用。（Berger–Moerdijk §1）。
  方針：既存の対称列で複体と作用をまとめる。
  規約：作用は有限全単射に関して共変。
  使われ方：各 arity の演算を取り出す。 -/
  sequence : _root_.SerrePositivity.SymmetricSequence (Complex A)
  /-- 概要：arity 1 の単位。（Berger–Moerdijk §1）。
  方針：テンソル単位から arity 1 の複体への射を指定する。
  規約：単位は chain map である。
  使われ方：左右の単位則と代数の単位作用に用いる。 -/
  unit : 𝟙_ (Complex A) ⟶ _root_.SerrePositivity.SymmetricSequence.level sequence 1
  /-- 概要：外側の位置 i へ arity n の演算を代入する chain map。（Berger–Moerdijk §1）。
  方針：一つの入力への代入を二因子のテンソルからの射で与える。
  規約：代入後の arity は m+n、n=0 を許す。
  使われ方：結合則と代数の演算の合成を述べる。 -/
  comp (m n : ℕ) (i : Fin (m + 1)) :
    _root_.SerrePositivity.SymmetricSequence.level sequence (m + 1) ⊗ _root_.SerrePositivity.SymmetricSequence.level sequence n ⟶
      _root_.SerrePositivity.SymmetricSequence.level sequence (m + n)
  /-- 概要：外側が単位演算であるときの左単位則。（Berger–Moerdijk §1）。
  方針：左単位子と arity の等式による移送で比較する。
  規約：arity 0 の演算にも適用する。
  使われ方：単位演算への代入を簡約する。 -/
  unit_comp (n : ℕ) :
    (unit ▷ _root_.SerrePositivity.SymmetricSequence.level sequence n) ≫ comp 0 n 0 ≫
      eqToHom (congrArg (_root_.SerrePositivity.SymmetricSequence.level sequence) (Nat.zero_add n)) =
      (λ_ (_root_.SerrePositivity.SymmetricSequence.level sequence n)).hom
  /-- 概要：内側が単位演算であるときの右単位則。（Berger–Moerdijk §1）。
  方針：右単位子を使って元の演算と比較する。
  規約：全ての入力位置で要求する。
  使われ方：単位演算の代入を簡約する。 -/
  comp_unit (m : ℕ) (i : Fin (m + 1)) :
    (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 1) ◁ unit) ≫ comp m 1 i =
      (ρ_ (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 1))).hom
  /-- 概要：内側の入力の置換は、その挿入区間の置換に一致する。（Berger–Moerdijk §1）。
  方針：挿入分解で内側の置換を出力の置換へ延長する。
  規約：区間外の入力は固定する。
  使われ方：coinvariant 関係と部分合成を両立させる。 -/
  inner_equivariance (m n : ℕ) (i : Fin (m + 1)) (τ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 1) ◁
      sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n τ)) ≫ comp m n i =
        comp m n i ≫ sequence.map
          (_root_.SerrePositivity.FiniteBijection.permutation (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ))
  /-- 概要：外側の入力の置換は、代入位置とその外の入力を対応して移す。（Berger–Moerdijk §1）。
  方針：挿入分解を外側の置換の前後で比較する。
  規約：挿入区間内部の順序を保つ。
  使われ方：外側の対称群作用と部分合成を両立させる。 -/
  outer_equivariance (m n : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) :
    (sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (m + 1) σ) ▷
      _root_.SerrePositivity.SymmetricSequence.level sequence n) ≫ comp m n (σ i) =
        comp m n i ≫ sequence.map
          (_root_.SerrePositivity.FiniteBijection.permutation (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ))
  /-- 概要：同じ入力の内側へさらに代入する入れ子の結合則。（Berger–Moerdijk §1）。
  方針：結合子と arity の等式による移送で二つの合成順序を比較する。
  規約：内側の代入位置は i+j。
  使われ方：複数の演算の代入の順序を比較する。 -/
  nested_assoc (m n k : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (comp m (n + 1) i ▷ _root_.SerrePositivity.SymmetricSequence.level sequence k) ≫
      comp (m + n) k ⟨i.val + j.val, by omega⟩ =
        (α_ (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 1))
          (_root_.SerrePositivity.SymmetricSequence.level sequence (n + 1)) (_root_.SerrePositivity.SymmetricSequence.level sequence k)).hom ≫
        (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 1) ◁ comp n k j) ≫
        comp m (n + k) i ≫
        eqToHom (congrArg (_root_.SerrePositivity.SymmetricSequence.level sequence) (Nat.add_assoc m n k).symm)
  /-- 概要：異なる入力への二つの代入は、内側二因子の Koszul 交換を介して可換である。（Berger–Moerdijk §1）。
  方針：結合子と対称性で二つの内側演算を交換する。
  規約：i<j を仮定し、空の入力区間も許す。
  使われ方：独立な演算の代入順序を比較する。 -/
  parallel_assoc (m n k : ℕ) (i j : Fin (m + 2)) (hij : i.val < j.val) :
    (comp (m + 1) n i ▷ _root_.SerrePositivity.SymmetricSequence.level sequence k) ≫
      eqToHom (congrArg (fun q => _root_.SerrePositivity.SymmetricSequence.level sequence q ⊗
        _root_.SerrePositivity.SymmetricSequence.level sequence k) (by omega : m + 1 + n = m + n + 1)) ≫
      comp (m + n) k ⟨j.val + n - 1, by omega⟩ =
        (α_ (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 2))
          (_root_.SerrePositivity.SymmetricSequence.level sequence n) (_root_.SerrePositivity.SymmetricSequence.level sequence k)).hom ≫
        (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 2) ◁
          (β_ (_root_.SerrePositivity.SymmetricSequence.level sequence n) (_root_.SerrePositivity.SymmetricSequence.level sequence k)).hom) ≫
        (α_ (_root_.SerrePositivity.SymmetricSequence.level sequence (m + 2))
          (_root_.SerrePositivity.SymmetricSequence.level sequence k) (_root_.SerrePositivity.SymmetricSequence.level sequence n)).inv ≫
        (comp (m + 1) k j ▷ _root_.SerrePositivity.SymmetricSequence.level sequence n) ≫
        eqToHom (congrArg (fun q => _root_.SerrePositivity.SymmetricSequence.level sequence q ⊗
          _root_.SerrePositivity.SymmetricSequence.level sequence n) (by omega : m + 1 + k = m + k + 1)) ≫
        comp (m + k) n ⟨i.val, by omega⟩ ≫
        eqToHom (congrArg (_root_.SerrePositivity.SymmetricSequence.level sequence) (by omega : m + k + n = m + n + k))

namespace Operad

variable {A : Type u} [CommRing A]

/-- 概要：対称 dg オペラッドの arity n の複体（Berger–Moerdijk §1）。
方針：既存の対称列の評価を使う。
規約：arity 0 も通常の複体である。
使われ方：演算・代数・オペラッド射の型を記述する。 -/
abbrev arity (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) : Complex A := _root_.SerrePositivity.SymmetricSequence.level P.sequence n

/-- 概要：arity n の対称群の右作用（Berger–Moerdijk §1）。
方針：対称列の共変な左作用を置換の逆元で右作用に直す。
規約：`rightAction (σ * τ) = rightAction σ ≫ rightAction τ`。
使われ方：自由代数の coinvariant の右作用として用いる。 -/
def rightAction (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) (σ : Equiv.Perm (Fin n)) : P.arity n ⟶ P.arity n :=
  P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ⁻¹)

/-- 概要：右作用の単位則（Berger–Moerdijk §1）。
方針：恒等全単射に対する関手の単位則を使う。
規約：右作用は逆元による変換を含む。
使われ方：arity ごとの対称群作用を計算する。 -/
@[simp]
lemma rightAction_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) : P.rightAction n 1 = 𝟙 (P.arity n) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.rightAction, inv_one, _root_.SerrePositivity.FiniteBijection.permutation_one]
  exact P.sequence.map_id _

/-- 概要：右作用の積は圏の合成と同順である（Berger–Moerdijk §1）。
方針：積の逆元と全単射の合成則を用いる。
規約：対称列から取り出す左作用とは合成順序が逆になる。
使われ方：オペラッドの通常の右作用の記法と対称列の API を接続する。 -/
lemma rightAction_mul (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    P.rightAction n (σ * τ) = P.rightAction n σ ≫ P.rightAction n τ := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.rightAction, mul_inv_rev, _root_.SerrePositivity.FiniteBijection.permutation_mul, Functor.map_comp]

/-- 概要：対称 dg オペラッド P の代数（Berger–Moerdijk §1）。
方針：各 arity の作用を chain map で与え、対称群の関係と部分合成との両立を要求する。
規約：arity 0 の作用を含み、係数を動かす際の符号は `tensorInsertionAction` に含まれる。
使われ方：E∞-dg 代数の圏と自由・忘却随伴を構成する。 -/
structure Algebra (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) where
  /-- 概要：代数の底の非有界コチェイン複体。（Berger–Moerdijk §1）。
  方針：既存の Complex A を底の対象として指定する。
  規約：微分は +1、次数は全整数。
  使われ方：忘却関手の対象成分となる。 -/
  carrier : Complex A
  /-- 概要：n 入力演算の作用の chain map。（Berger–Moerdijk §1）。
  方針：演算の複体と底の複体のテンソル冪から射を与える。
  規約：n=0 の作用も指定する。
  使われ方：代数射の保存則と自由代数の普遍性に用いる。 -/
  action (n : ℕ) : P.arity n ⊗ _root_.SerrePositivity.TensorPowers.power carrier n ⟶ carrier
  /-- 概要：作用は coinvariant の対称群の関係を満たす。（Berger–Moerdijk §1）。
  方針：係数と入力の同時置換を作用の前に合成する。
  規約：入力の置換は Koszul 符号を含む。
  使われ方：作用を Schur 対象からの射へ降ろす。 -/
  equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ⊗ₘ
      (_root_.SerrePositivity.TensorPowers.permutationAction carrier n σ).asIso.hom) ≫ action n = action n
  /-- 概要：arity 1 の単位演算は恒等演算として作用する。（Berger–Moerdijk §1）。
  方針：単位子と一次テンソル冪の同型で恒等演算と比較する。
  規約：作用の底の複体への射として等式を要求する。
  使われ方：自由・忘却随伴の単位則に用いる。 -/
  unit_action :
    (P.unit ▷ _root_.SerrePositivity.TensorPowers.power carrier 1) ≫ action 1 =
      (λ_ (_root_.SerrePositivity.TensorPowers.power carrier 1)).hom ≫ (_root_.SerrePositivity.TensorPowers.oneIso carrier).hom
  /-- 概要：オペラッドでの部分合成と、入力への演算の代入は同じ作用を与える。（Berger–Moerdijk §1）。
  方針：tensorInsertionAction で入力への代入を記述する。
  規約：係数の移動の Koszul 符号を保つ。
  使われ方：代数の結合則として用いる。 -/
  comp_action (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ _root_.SerrePositivity.TensorPowers.power carrier (m + n)) ≫ action (m + n) =
      (α_ (P.arity (m + 1)) (P.arity n) (_root_.SerrePositivity.TensorPowers.power carrier (m + n))).hom ≫
      (P.arity (m + 1) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction carrier (P.arity n) m n i (action n)) ≫
      action (m + 1)

/-- 概要：オペラッド代数の射（Berger–Moerdijk §1）。
方針：底の chain map が全 arity の演算の作用を保つことを要求する。
規約：arity 0 の演算も保存する。
使われ方：E∞-dg 代数の圏の射となる。 -/
@[ext]
structure AlgebraHom {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} (X Y : P.Algebra) where
  /-- 概要：底の複体射。（Berger–Moerdijk §1）。
  方針：底の非有界複体の間の chain map を指定する。
  規約：次数を保ち微分と可換である。
  使われ方：忘却関手の射成分となる。 -/
  hom : X.carrier ⟶ Y.carrier
  /-- 概要：底の射は全 arity の作用を保つ。（Berger–Moerdijk §1）。
  方針：底の射のテンソル冪を入力側に合成して比較する。
  規約：arity 0 の作用も保存する。
  使われ方：代数射の恒等射と合成の保存則に用いる。 -/
  comm (n : ℕ) : X.action n ≫ hom =
    (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map hom n) ≫ Y.action n

namespace Algebra

variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：オペラッド代数と作用を保つ chain map の圏（Berger–Moerdijk §1）。
方針：底の chain map の恒等射と合成を用い、テンソル冪の関手性で保存則を示す。
規約：底の複体の圏と同じ Hom 宇宙を持つ。
使われ方：自由・忘却随伴と転送モデル構造の値域となる。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instCategory : Category P.Algebra where
  Hom X Y := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom X Y
  id X := { hom := 𝟙 X.carrier
            comm n := by simp only [_root_.SerrePositivity.TensorPowers.map_id, Category.comp_id,
              tensorHom_id, id_whiskerRight, Category.id_comp] }
  comp f g := {
    hom := f.hom ≫ g.hom
    comm n := by
      rw [← Category.assoc, f.comm, Category.assoc, g.comm]
      simp only [_root_.SerrePositivity.TensorPowers.map_comp, ← Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp] }
  id_comp f := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; exact Category.assoc f.hom g.hom h.hom

/-- 概要：オペラッド代数から底の複体への忘却関手（Berger–Moerdijk §1）。
方針：対象を carrier、射を hom に送る。
規約：この段ではモデル構造を仮定しない。
使われ方：自由代数の右随伴と転送モデル構造の忘却関手として用いる。 -/
def forget (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : P.Algebra ⥤ Complex A where
  obj X := X.carrier
  map f := f.hom

/-- 概要：忘却関手は忠実（Berger–Moerdijk §1）。
方針：代数射は底の chain map とその保存則の証明からなる。
規約：作用を保存するという性質を射の追加データと区別する。
使われ方：代数射の等式を底の複体射で判定する。 -/
instance forget_faithful (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).Faithful where
  map_injective h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext h

end Algebra

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
