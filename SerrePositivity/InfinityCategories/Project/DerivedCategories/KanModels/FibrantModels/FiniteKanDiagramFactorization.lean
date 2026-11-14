module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanFiniteFactorization
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits

/-! # Kan 置換内の有限二図式の共通因子化

概要：同じ有限形状の二図式を、元の一つの有限部分複体の Kan 置換へ同時に下ろす。
方針：二図式を余積からの一射にまとめ、連続 Kan 置換の有限因子化を使う。
規約：二つの合成は元の図式と厳密に一致する。使われ方：有限ホモトピー類の単射側。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet

/-- 有限形状の二図式は、同じ有限部分複体の Kan 置換を経由する。 -/
lemma continuousKanFinitePair_factorization {K E : SSet.{u}} [K.Finite]
    (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) :
    ∃ A : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex E,
      ∃ a b : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj A.val,
        a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map A.val.ι = f ∧
          b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map A.val.ι = g := by
  obtain ⟨A, v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_finite_factorization (coprod.desc f g)
  refine ⟨A, coprod.inl ≫ v, coprod.inr ≫ v, ?_, ?_⟩
  · rw [Category.assoc, hv, coprod.inl_desc]
  · rw [Category.assoc, hv, coprod.inr_desc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
