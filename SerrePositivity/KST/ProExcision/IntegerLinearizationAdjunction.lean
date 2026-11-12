module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 任意の宇宙の自由整数加群の実随伴

概要：既存の非被約自由化に実自由・忘却随伴を構成する。
方針：基底元での評価と実線形拡張を互いの逆として使う。
規約：KST Appendix A の C(-)。係数 ℤ と基底の宇宙を独立に保つ。
使われ方：実鎖模型の rank 余極限保存。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits

/-- 概要：自由整数加群からの射と基底上の実写像の実全単射。
方針：基底元で評価し、逆は既存の実線形拡張とする。
規約：KST App. A。使われ方：自由化の実随伴の Hom 同型。 -/
def integerLinearizationHomEquiv (X : Type u) (M : ModuleCat.{u} ℤ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.obj X ⟶ M) ≃ (X ⟶ (forget (ModuleCat.{u} ℤ)).obj M) where
  toFun f := TypeCat.ofHom (fun x ↦ f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  invFun f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun x ↦ f x)
  left_inv f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
    intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator (fun x ↦ f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) x
  right_inv f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator (fun x ↦ f x) x

/-- 概要：非被約自由整数加群関手と忘却関手の実随伴。
方針：実 Hom 同型の二つの自然性を基底元で検証する。
規約：KST App. A、全ての基底宇宙。使われ方：実余極限の保存。 -/
def integerLinearizationAdjunction : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.{u} ⊣ forget (ModuleCat.{u} ℤ) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := integerLinearizationHomEquiv
    homEquiv_naturality_left_symm := by
      intro X Y M f g
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
      intro x
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun y ↦ g (f y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun y ↦ g y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator]
    homEquiv_naturality_right := by
      intro X M N f g
      apply ConcreteCategory.hom_ext
      intro x
      rfl }

/-- 概要：非被約自由整数加群関手は順序余極限を保存する。
方針：実自由・忘却随伴の左随伴の保存性を用いる。
規約：SW92 Lemma 1.4。使われ方：実自由整数鎖複体の順序余極限。 -/
instance integerLinearization_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.{u} := by
  have : PreservesColimitsOfSize.{0, 0} _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.{u} :=
    integerLinearizationAdjunction.leftAdjoint_preservesColimits
  infer_instance

end SerrePositivity.KST.ProExcision
