module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorColimit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition

/-!
模型。文献の定義との比較は後で
# Schur 入力のテンソル冪の余極限表示と降下

概要：Berger–Moerdijk §1 の自由代数の作用の降下に用いる余極限を構成する。
方針：有限全単射の独立な直積上で、Schur 図式の外部テンソル積を取る。
規約：頂点は既存の Schur 対象のテンソル冪。代数構造の存在は仮定しない。
使われ方：生成射上の等変な演算を実際の Schur 入力からの chain map へ降ろす。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：独立な Schur 入力の各段を表す外部テンソル図式（Berger–Moerdijk §1）。
方針：Schur 図式の独立な n 個のコピーのテンソルを取る。
規約：添字は有限全単射の直積であり、arity 0 も含む。
使われ方：自由代数の作用を余錐の自然性として構成する。 -/
abbrev schurTensorDiagram (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K : Complex A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex _root_.SerrePositivity.FiniteBijection n ⥤ Complex A :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexDiagram (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K) n

/-- 概要：Schur 入力のテンソル冪を頂点とする標準余錐（Berger–Moerdijk §1）。
方針：Schur 余極限の構造射を独立な入力ごとにテンソルする。
規約：空の入力族では単位複体を頂点とする。
使われ方：作用の降下をテンソル冪からの射として与える。 -/
def schurTensorCocone (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K : Complex A) (n : ℕ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexCocone (colimit.cocone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)) n

/-- 概要：標準 Schur テンソル余錐は余極限である（Berger–Moerdijk §1）。
方針：Schur 余極限と有限外部テンソル積の余極限保存を組み合わせる。
規約：底の環は任意の可換環でよく、cofibrancy を仮定しない。
使われ方：等変な生成射族から自由代数の作用の chain map を得る。 -/
def schurTensorCoconeIsColimit (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K : Complex A) (n : ℕ) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorCocone P K n) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndexCoconeIsColimit (colimit.isColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P K)) n

/-- 概要：独立な Schur 入力の段からテンソル冪への標準生成射（Berger–Moerdijk §1）。
方針：標準のテンソル余錐の構造射を取る。
規約：添字は各入力の有限集合の組。
使われ方：降下させた作用を各入力の生成元で計算する。 -/
def schurTensorLeg (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K : Complex A) (n : ℕ)
    (j : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex _root_.SerrePositivity.FiniteBijection n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj j ⟶ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K) n :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorCocone P K n).ι.app j

/-- 概要：左に固定係数を付けた Schur テンソル図式の余錐（Berger–Moerdijk §1）。
方針：標準余錐を左テンソル関手で写す。
規約：係数複体は任意でよい。
使われ方：P(n) を係数とする自由代数の n 入力演算を降ろす。 -/
def schurTensorLeftCocone (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C : Complex A) (n : ℕ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n ⋙ tensorLeft C) :=
  (tensorLeft C).mapCocone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorCocone P K n)

/-- 概要：固定係数付きの Schur テンソル余錐も余極限である（Berger–Moerdijk §1）。
方針：閉モノイダル構造による左テンソル関手の余極限保存を使う。
規約：係数に平坦性や cofibrancy を追加しない。
使われ方：全入力へのオペラッド合成から自由代数の作用を作る。 -/
def schurTensorLeftCoconeIsColimit (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C : Complex A) (n : ℕ) :
    IsColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorLeftCocone P K C n) :=
  isColimitOfPreserves (tensorLeft C) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorCoconeIsColimit P K n)

/-- 概要：等変な独立入力の射族を Schur テンソル冪からの射へ降ろす（Berger–Moerdijk §1）。
方針：射族の自然性から余錐を作り、固定係数付きの余極限の降下射を取る。
規約：自然性は各入力の全単射について要求する。
使われ方：自由代数の作用を生成射上の式から構成する。 -/
def schurTensorDesc (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A) (n : ℕ)
    (f : ∀ j, C ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj j ⟶ Y)
    (hf : ∀ {j k} (σ : j ⟶ k), (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σ) ≫ f k = f j) :
    C ⊗ power ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P).obj K) n ⟶ Y :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorLeftCoconeIsColimit P K C n).desc {
    pt := Y
    ι := {
      app := f
      naturality := fun {j k} σ => by
        change (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σ) ≫ f k = f j ≫ 𝟙 Y
        rw [Category.comp_id]
        exact hf σ } }

/-- 概要：Schur テンソル冪への降下射は指定した生成射族に一致する（Berger–Moerdijk §1）。
方針：余極限の構造射と降下射の合成則を用いる。
規約：固定係数は左側に置く。
使われ方：自由代数の作用の生成射上の式を検証する。 -/
@[reassoc]
lemma schurTensorLeg_desc (P : _root_.SerrePositivity.SymmetricSequence (Complex A)) (K C Y : Complex A) (n : ℕ)
    (f : ∀ j, C ⊗ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).obj j ⟶ Y)
    (hf : ∀ {j k} (σ : j ⟶ k), (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDiagram P K n).map σ) ≫ f k = f j)
    (j : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorIndex _root_.SerrePositivity.FiniteBijection n) :
    (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorLeg P K n j) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorDesc P K C Y n f hf = f j :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurTensorLeftCoconeIsColimit P K C n).fac _ j

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
