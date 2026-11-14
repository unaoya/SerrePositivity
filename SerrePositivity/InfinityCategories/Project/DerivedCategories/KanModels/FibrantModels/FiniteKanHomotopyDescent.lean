module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.FiniteKanDiagramFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-! # 有限パラメータの Kan ホモトピーの相対下降

概要：元の有限部分に端点を持つ Kan ホモトピーを、共通の有限な後続部分に下ろす。
方針：円柱の二端を余積で指定し、有限な相対因子化で両端を厳密に保持する。
規約：ホモトピー全体も元の全時刻の射へ合成される。使われ方：有限写像空間の単射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial

/-- 有限パラメータの指定二端点付きホモトピーは、有限部分の後続段に実現できる。 -/
lemma continuousKanFiniteHomotopy_descent {K Q : SSet.{u}} [K.Finite]
    (B : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex Q) (f g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj B.val)
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map B.val.ι)
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map B.val.ι)) :
    ∃ (C : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex Q) (v : B ⟶ C),
      ∃ R : SSet.Homotopy
        (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (Subcomplex.homOfLE (leOfHom v)))
        (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (Subcomplex.homOfLE (leOfHom v))),
          R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map C.val.ι = H.h := by
  let i : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) := coprod.desc SSet.ι₀ SSet.ι₁
  have hi : coprod.desc f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map B.val.ι = i ≫ H.h := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, coprod.inl_desc]
      exact H.h₀.symm
    · rw [← Category.assoc, coprod.inr_desc, ← Category.assoc, coprod.inr_desc]
      exact H.h₁.symm
  obtain ⟨C, v, h, hh, hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finiteSubcomplex_relative_factorization_after_preserving_functor
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement Q i B (coprod.desc f g) H.h hi
  let R : SSet.Homotopy
      (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (Subcomplex.homOfLE (leOfHom v)))
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (Subcomplex.homOfLE (leOfHom v))) := {
    h := h
    h₀ := by
      change SSet.ι₀ ≫ h = f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (Subcomplex.homOfLE (leOfHom v))
      have h₀ := congrArg (fun z => coprod.inl ≫ z) hh
      simpa only [i, ← Category.assoc, coprod.inl_desc] using h₀
    h₁ := by
      change SSet.ι₁ ≫ h = g ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (Subcomplex.homOfLE (leOfHom v))
      have h₁ := congrArg (fun z => coprod.inr ≫ z) hh
      simpa only [i, ← Category.assoc, coprod.inr_desc] using h₁
    rel := by
      ext n s
      exact False.elim s.1.property }
  exact ⟨C, v, R, hH⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
