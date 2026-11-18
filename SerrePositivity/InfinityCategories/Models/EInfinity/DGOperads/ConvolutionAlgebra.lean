module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraFirstComposition

/-!
模型。文献の定義との比較は後で
# 内部 Hom の convolution 代数

概要：Berger–Fresse §3.1 の Hopf オペラッドの余代数と代数から convolution 代数を作る。
方針：評価後の先頭合成則を転置し、等変性で全位置の合成則へ拡張する。
規約：任意の可換環と非有界複体を扱う。
使われ方：余代数区間を始域とする functorial path object の代数となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：convolution 演算は先頭位置の部分合成則を満たす（BF §3.1）。
方針：右 tensor 転置の入力自然性で評価後の合成則を戻す。
規約：入力数零の内側演算も含む。
使われ方：等変性による全位置の代数公理の判定へ適用する。 -/
lemma convolutionAction_comp_zero (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra)
    (B : P.Algebra) (m n : ℕ) :
    (P.comp m n 0 ▷ power (homComplex A H.carrier B.carrier) (m + n)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n)
      (power (homComplex A H.carrier B.carrier) (m + n))).hom ≫
      (P.arity (m + 1) ◁
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (homComplex A H.carrier B.carrier) (P.arity n) m n 0
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B (m + 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction, ← curryRight_naturality_source, tensorHom_id,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction_comp_zero, ← comp_whiskerRight_assoc,
    ← tensorHom_id, curryRight_naturality_source]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction]

/-- 概要：内部 Hom は Hopf オペラッドの代数をなす（BF §3.1）。
方針：単位・等変性・先頭合成則を全位置の代数公理へ束ねる。
規約：余代数・代数の cofibrancy やモデル構造を仮定しない。
使われ方：区間から代数の path object を作る本体となる。 -/
def convolutionAlgebra (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra) : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofFirstComposition P (homComplex A H.carrier B.carrier) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_equivariance hP H B) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_comp_zero hP H B)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_unit hP H B)

/-- 概要：convolution は任意の入力位置で部分合成を保つ（BF §3.1）。
方針：構成した代数の全位置の合成公理を取り出す。
規約：先頭以外の位置も同じ標準の代入射で述べる。
使われ方：内部 Hom の演算と既存のオペラッド代数 API を照合する。 -/
lemma convolutionAction_comp (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra) (B : P.Algebra)
    (m n : ℕ) (i : Fin (m + 1)) :
    (P.comp m n i ▷ power (homComplex A H.carrier B.carrier) (m + n)) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B (m + n) =
    (α_ (P.arity (m + 1)) (P.arity n)
      (power (homComplex A H.carrier B.carrier) (m + n))).hom ≫
      (P.arity (m + 1) ◁
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction (homComplex A H.carrier B.carrier) (P.arity n) m n i
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B (m + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP H B).comp_action m n i

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
