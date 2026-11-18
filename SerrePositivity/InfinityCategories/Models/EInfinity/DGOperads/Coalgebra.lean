module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertion

/-!
模型。文献の定義との比較は後で
# オペラッドの余代数

概要：Berger–Fresse §3.1 の P-coalgebra を非有界複体上で定義する。
方針：P(n) ⊗ H → H の n 重テンソルという余演算に単位・等変性・部分合成則を課す。
規約：arity 0 を含み、モデル構造や path object の存在をデータに含めない。
使われ方：Hopf オペラッドによる convolution と E-coalgebra 区間の界面となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：対称 dg オペラッド P の余代数（Berger–Fresse §3.1）。
方針：各 arity の余演算を chain map として持ち、その代入則を要求する。
規約：余演算の係数に P の同じ対称列を用い、出力の置換は共変に作用する。
使われ方：E-coalgebra 区間と内部 Hom の convolution の係数となる。 -/
structure Coalgebra (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) where
  /-- 概要：余代数の底の非有界複体（BF §3.1）。
  方針：既存の整数コチェイン複体を指定する。
  規約：微分は +1。
  使われ方：区間や内部 Hom の始域となる。 -/
  carrier : Complex A
  /-- 概要：n 出力の余演算（BF §3.1）。
  方針：演算の係数と底の複体から n 重テンソルへ写す。
  規約：n=0 の出力はテンソル単位 A[0]。
  使われ方：convolution の n 入力演算に評価点を分配する。 -/
  coaction (n : ℕ) : P.arity n ⊗ carrier ⟶ power carrier n
  /-- 概要：余演算の対称群等変性（BF §3.1）。
  方針：係数の置換を出力の同じ置換へ移す。
  規約：出力置換は Koszul 符号を含む。
  使われ方：convolution の対称性を保証する。 -/
  equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ▷ carrier) ≫ coaction n =
      coaction n ≫ (permutationAction carrier n σ).asIso.hom
  /-- 概要：単位演算は恒等余演算として作用する（BF §3.1）。
  方針：一次テンソル冪と底の複体の同型で比較する。
  規約：テンソル単位の左単位子を明示する。
  使われ方：convolution の単位則を保証する。 -/
  unit_coaction : (P.unit ▷ carrier) ≫ coaction 1 ≫ (oneIso carrier).hom =
    (λ_ carrier).hom
  /-- 概要：部分合成の余演算は一つの出力への余演算の代入である（BF §3.1）。
  方針：外側の余演算を先に適用し、指定出力を内側の余演算で置き換える。
  規約：内側の係数を前に出す交換を明示し、arity 0 も許す。
  使われ方：convolution の合成則を保証する。 -/
  comp_coaction (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ carrier) ≫ coaction (m + n) =
      ((β_ (P.arity (m + 1)) (P.arity n)).hom ▷ carrier) ≫
      (α_ (P.arity n) (P.arity (m + 1)) carrier).hom ≫
      (P.arity n ◁ coaction (m + 1)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction carrier (P.arity n) m n i (coaction n)

/-- 概要：P-coalgebra の射（Berger–Fresse §3.1）。
方針：底の chain map が全ての余演算を保つことを要求する。
規約：arity 0 の余演算の保存を含む。
使われ方：区間の端点・収縮を余代数射として指定する。 -/
@[ext]
structure CoalgebraHom {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} (X Y : P.Coalgebra) where
  /-- 概要：底の複体射（BF §3.1）。
  方針：同じ基礎環上の chain map を指定する。
  規約：次数を保つ。
  使われ方：内部 Hom の前合成を誘導する。 -/
  hom : X.carrier ⟶ Y.carrier
  /-- 概要：底の射は全余演算を保存する（BF §3.1）。
  方針：余演算の前の底の射と出力のテンソル冪で比較する。
  規約：係数の P(n) 因子は恒等のまま。
  使われ方：convolution の前合成が P 代数射になることを示す。 -/
  comm (n : ℕ) : (P.arity n ◁ hom) ≫ Y.coaction n =
    X.coaction n ≫ _root_.SerrePositivity.TensorPowers.map hom n

namespace Coalgebra

variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：P-coalgebra と余演算を保つ chain map の圏（BF §3.1）。
方針：底の恒等射・合成とテンソル冪の関手性を使う。
規約：複体と同じ Hom 宇宙を持つ。
使われ方：区間とその端点を関手的に扱う。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Coalgebra.instCategory : Category P.Coalgebra where
  Hom X Y := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom X Y
  id X := { hom := 𝟙 X.carrier
            comm n := by simp only [whiskerLeft_id, Category.id_comp,
              _root_.SerrePositivity.TensorPowers.map_id, Category.comp_id] }
  comp f g := {
    hom := f.hom ≫ g.hom
    comm n := by
      rw [whiskerLeft_comp, Category.assoc, g.comm, ← Category.assoc, f.comm]
      simp only [Category.assoc, _root_.SerrePositivity.TensorPowers.map_comp] }
  id_comp f := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext; exact Category.id_comp f.hom
  comp_id f := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext; exact Category.comp_id f.hom
  assoc f g h := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext; exact Category.assoc f.hom g.hom h.hom

/-- 概要：余代数から複体への忘却関手（BF §3.1）。
方針：carrier と底の射へ写す。
規約：モデル構造を仮定しない。
使われ方：余代数区間の複体としての性質を記述する。 -/
def forget (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : P.Coalgebra ⥤ Complex A where
  obj X := X.carrier
  map f := f.hom

/-- 概要：余代数の忘却関手は忠実（BF §3.1）。
方針：射の追加条件は命題であることを使う。
規約：対象の余代数構造は忘却される。
使われ方：余代数射の等式を複体射で検証する。 -/
instance forget_faithful (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Coalgebra.forget P).Faithful where
  map_injective h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraHom.ext h

end Coalgebra

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
