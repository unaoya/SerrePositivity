module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# 元の導来比較の正方形からホモロジーの正方形へ

## 概要
元の導来圏の射の等式を、元の複体のホモロジーの等式として読む。

## 方針
元の局所化のホモロジー分解同型の自然性を使う。

## 規約
新しいホモロジー同型を選ばず、Mathlibの同じ標準比較を保持する。

## 使われ方
HT04.R2の指定e_targetを使った零次・一次の正方形を運ぶ。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {B : Type u} [CommRing B]

/-- 元の局所化の標準ホモロジー比較を通した射の正方形。 -/
theorem derivedHomologyComparison_square
    {K L : DerivedCategory (ModuleCat.{u} B)}
    {V W : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : K ⟶ L) (g : V ⟶ W) (s : K ⟶ DerivedCategory.Q.obj V)
    (t : L ⟶ DerivedCategory.Q.obj W) (hf : f ≫ t = s ≫ DerivedCategory.Q.map g) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map f ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map t ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).hom.app W =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map s ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).hom.app V ≫
      homologyMap g i := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) i
  have h := congrArg (fun q => H.map q ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) i).hom.app W) hf
  simpa only [H, Functor.map_comp, Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality] using h

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
