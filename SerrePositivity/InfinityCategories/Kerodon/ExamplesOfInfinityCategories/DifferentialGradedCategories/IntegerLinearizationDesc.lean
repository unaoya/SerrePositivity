module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedSpace

/-!
# 自由整数加群からの線形拡張

概要：任意の基底上の写像を自由整数加群の射へ拡張する。
方針：有限台関数の線形な和を使う。
規約：KST Lemma A.4 の線形係数の持ち上げ。非被約な自由化を保つ。
使われ方：語を固定した bar の区間写像の線形な構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory

/-- 概要：基底上の任意の写像の整数線形拡張。
方針：有限台関数の線形な lift。
規約：KST Lemma A.4、任意の宇宙の基底。使われ方：bar への線形な移送。 -/
def integerLinearizationDesc {X : Type u} {M : ModuleCat.{u} ℤ} (f : X → M) :
    integerLinearization.obj X ⟶ M := ModuleCat.ofHom (Finsupp.lift M ℤ X f)

/-- 概要：整数線形拡張は基底上で元の写像に一致する。
方針：係数1の単項有限台関数を評価する。
規約：KST Lemma A.4。使われ方：自然性と両端条件の基底上の証明。 -/
@[simp] lemma integerLinearizationDesc_generator {X : Type u} {M : ModuleCat.{u} ℤ}
    (f : X → M) (x : X) : integerLinearizationDesc f (integerGenerator x) = f x := by
  dsimp [integerLinearizationDesc, integerGenerator]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  · exact M.isModule.one_smul (f x)
  · exact M.isModule.zero_smul (f x)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
