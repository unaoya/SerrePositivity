module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedQuillenFrameInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-!
概要：任意の元の関手上の共通 frame 比較の二つの実際の Hom 射をホモトピー同値と証明する。
方針：既存の共通 Reedy cofibrant 族と弱比較を、固定 Quillen 類での frame 不変性に入力する。
規約：二変数の自然変換と元の比較射を保持。使われ方：Quillen 左像 frame と標準導来 Hom の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w t
open CategoryTheory Limits HomotopicalAlgebra SSet
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [ModelCategory C]
  {B : Type w} [Category.{t} B]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex) (H : B ⥤ C)
  (P : B ⥤ (SimplexCategory ⥤ C)) (a : P ⟶ H ⋙ Functor.const SimplexCategory)
  (ha : ∀ X n, weakEquivalences C ((a.app X).app n))

include ha

/-- 元の標準解消から同じ共通 frame への Hom 自然変換は、各成分でホモトピー同値。 -/
lemma fixedFrameOverFunctor_homLeft_homotopyEquivalence (X : Bᵒᵖ) (Y : C) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((FrameOverFunctor.homLeft cof q H P a).app X).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHomMap_homotopyEquivalence ((FrameOverFunctor.left cof q H P a).app X.unop)
    (FrameOverFunctor.commonObj_cofibrant cof q H P a X.unop) (q.cofibrant (H.obj X.unop))
    (FrameOverFunctor.commonObj_homotopicallyConstant cof q H P a ha X.unop)
    (q.atObject (H.obj X.unop)).homotopicallyConstant
    (FrameOverFunctor.left_weakEquivalence cof q H P a ha X.unop) Y

/-- 元の比較 frame から同じ共通 frame への Hom 自然変換も、その同じ射でホモトピー同値。 -/
lemma fixedFrameOverFunctor_homRight_homotopyEquivalence
    (hP : ∀ X, reedyLeft simplex (cofibrations C) (initial.to (P.obj X)))
    (hcP : ∀ X {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C ((P.obj X).map f))
    (X : Bᵒᵖ) (Y : C) [IsFibrant Y] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (((FrameOverFunctor.homRight cof q H P a).app X).app Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.frameHomMap_homotopyEquivalence ((FrameOverFunctor.right cof q H P a).app X.unop)
    (FrameOverFunctor.commonObj_cofibrant cof q H P a X.unop) (hP X.unop)
    (FrameOverFunctor.commonObj_homotopicallyConstant cof q H P a ha X.unop) (hcP X.unop)
    (FrameOverFunctor.right_weakEquivalence cof q H P a X.unop) Y

end
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
