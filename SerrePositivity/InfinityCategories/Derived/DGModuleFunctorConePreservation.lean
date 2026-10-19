module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorConeZeroCorner

/-! # dg 加群関手は実標準 cofiber 四角形を保つ

概要：標準 cone 四角形の実関手像は標準像と関手同型で、実押し出しである。
方針：cone 終点同型と零角変更同型を合成し、native nerve の後合成と照合する。
規約：標準四角形の保存を主張する。全 cofiber への拡張は選択独立性を使う。使われ方：β3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve

/-- 終点と零角を含む、標準像と実関手像の全四角形の関手同型。 -/
def dgModuleFunctorConeDataFunctorIso
    (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
    (E : Type w) [DGCategory A E] [Small.{u} E]
    (F : DGFunctor A (RightModule A D) (RightModule A E))
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    FunctorIso (dgModuleConeSquare A E (F.onClosed.map f))
      ((dgModuleConeSquareData A D f).map F).square :=
  (dgModuleFunctorConeSquareModelFunctorIso A D E F f).trans
    (dgModuleFunctorConeSquareZeroFunctorIso A D E F f)

variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {M N : ModuleCategory A D}

/-- native nerve の実関手像と標準像の全四角形の関手同型。 -/
def dgModuleFunctorConeSquareFunctorIso (f : M ⟶ N) :
    FunctorIso (dgModuleConeSquare A E (F.onClosed.map f))
      (dgModuleConeSquare A D f ≫ dgNerve.map F) := by
  have h := dgModuleFunctorConeDataFunctorIso A D E F f
  rw [DGModuleSquareData.map_square, dgModuleConeSquareData_square] at h
  exact h

/-- 任意の dg 加群値 dg 関手は標準 cofiber の実押し出し四角形を保つ。 -/
theorem dgModuleFunctorConeSquare_isPushout (f : M ⟶ N) :
    IsPushoutSquare (dgModuleConeSquare A D f ≫ dgNerve.map F) :=
  (dgModuleConeSquare_isPushout A E (F.onClosed.map f)).of_functorIso
    (dgModuleFunctorConeSquareFunctorIso A D E F f)

end SerrePositivity.InfinityCategories
