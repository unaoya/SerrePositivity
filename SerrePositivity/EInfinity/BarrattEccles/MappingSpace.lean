module

public import SerrePositivity.EInfinity.BarrattEccles.MappingFactorizations
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
# 実際の E 代数の homotopy function complex

概要：BM 命題 4.1・Hovey §5 の関手的な分解から E 代数の導来写像空間を構成する。
方針：始域の余単体的 frame と終域の fibrant 置換の実際の Hom を使う。
規約：元の E 代数に cofibrancy を要求せず、単体集合のモデル構造を仮定しない。
使われ方：E2a-5 の Map^h と E2b の写像空間の界面。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

variable (A : Type u) [CommRing A]

/-- 概要：任意の二つの E 代数の関手的な導来写像空間（BM 命題 4.1、Hovey §5）。
方針：具体的な二つの関手的分解を既存の frame Hom へ代入する。
規約：始域は反変、終域は共変、実際の単体集合に値を取る。
使われ方：π₀ の Hom 比較と homotopy 極限の写像空間による検証。 -/
def mappingSpace : (operad A).Algebraᵒᵖ ⥤ (operad A).Algebra ⥤ SSet.{u} := by
  let := modelCategory A
  exact chosenResolutionHom (mappingCofibrantFactorization A) (mappingFibrantFactorization A)

/-- 概要：構成した E 代数の導来写像空間は Kan 複体（Hovey §5）。
方針：余単体的 frame のホーン持ち上げと終域の fibrant 置換を使う。
規約：どちらの元の E 代数にも cofibrancy・fibrancy を仮定しない。
使われ方：E2a-5 の写像空間と π₀ の射の解釈。 -/
lemma mappingSpace_kanComplex (X : (operad A).Algebraᵒᵖ) (Y : (operad A).Algebra) :
    SSet.KanComplex (((mappingSpace A).obj X).obj Y) := by
  let := modelCategory A
  exact chosenResolutionHom_kanComplex
    (mappingCofibrantFactorization A) (mappingFibrantFactorization A) X Y

end SerrePositivity.EInfinity.BarrattEccles
