module
public import SerrePositivity.KST.ProExcision.ActionBarFibers
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedSpace

/-!
# 語を固定した係数包含の整数線形化

概要：作用 bar の語を固定した係数の包含を自由整数加群の射にする。
方針：係数の作用と単体射を自由化し、幾何的な包含の自然性を移す。
規約：KST Lemma A.4 の非被約な線形 bar。
使われ方：単体的に自然な区間写像の持ち上げ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
variable {G : SimplicialObject MonCat.{u}} {X : SSet.{u}}

/-- 概要：G の各元の作用を自由整数加群へ送る。
方針：作用する集合の自己写像を自由化する。
規約：KST Definition A.3。使われ方：区間写像の G 同変条件。 -/
def linearizedSetAction (A : SimplicialSetAction G X) (n : SimplexCategoryᵒᵖ) (a : G.obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (X.obj n) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (X.obj n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (↾(A.action n a))

/-- 概要：語を固定した係数の包含の整数線形化。
方針：基底の包含を自由化する。
規約：KST Lemma A.4。使われ方：線形な係数の値を bar へ移す。 -/
def linearizedActionBarFiber (A : SimplicialSetAction G X) (n : SimplexCategoryᵒᵖ)
    (w : (monoidBar G).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj (X.obj n) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj ((setActionBar A).obj n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (↾(setActionBarFiberSection A n w))

/-- 概要：線形化した係数包含は単体射の prefix 作用の式を満たす。
方針：幾何的な包含の自然性に自由化関手を適用する。
規約：KST Lemma A.4、全ての面と退化。
使われ方：線形な区間写像の bar への持ち上げの自然性。 -/
theorem linearizedActionBarFiber_naturality (A : SimplicialSetAction G X)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (w : (monoidBar G).obj n) :
    linearizedActionBarFiber A n w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((setActionBar A).map f) =
      linearizedSetAction A n (barWordFacePrefix f w) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (X.map f) ≫
        linearizedActionBarFiber A m ((monoidBar G).map f w) := by
  have he : (↾(setActionBarFiberSection A n w)) ≫ (setActionBar A).map f =
      (↾(A.action n (barWordFacePrefix f w))) ≫ X.map f ≫
        (↾(setActionBarFiberSection A m ((monoidBar G).map f w))) := by
    apply ConcreteCategory.hom_ext
    intro x
    exact setActionBarFiberSection_naturality A f w x
  have hh := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map he
  simp only [CategoryTheory.Functor.map_comp] at hh
  exact hh

end SerrePositivity.KST.ProExcision
