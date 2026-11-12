module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorConeZeroCorner

/-! # dg 加群関手は実標準 cofiber 四角形を保つ

概要：標準 cone 四角形の実関手像は標準像と関手同型で、実押し出しである。
方針：cone 終点同型と零角変更同型を合成し、native nerve の後合成と照合する。
規約：標準四角形の保存を主張する。全 cofiber への拡張は選択独立性を使う。使われ方：β3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded

/-- 終点と零角を含む、標準像と実関手像の全四角形の関手同型。 -/
def dgModuleFunctorConeDataFunctorIso
    (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
    (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E))
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A E (F.onClosed.map f))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A D f).map F).square :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareModelFunctorIso A D E F f).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquareZeroFunctorIso A D E F f)

variable (A : Type u) [CommRing A] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E))
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- native nerve の実関手像と標準像の全四角形の関手同型。 -/
def dgModuleFunctorConeSquareFunctorIso (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A E (F.onClosed.map f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  have h := dgModuleFunctorConeDataFunctorIso A D E F f
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.map_square, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData_square] at h
  exact h

/-- 任意の dg 加群値 dg 関手は標準 cofiber の実押し出し四角形を保つ。 -/
theorem dgModuleFunctorConeSquare_isPushout (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A E (F.onClosed.map f)).of_functorIso
    (dgModuleFunctorConeSquareFunctorIso A D E F f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
