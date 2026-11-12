module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：区間境界上の任意の図式は元の二端点だけで厳密に決まる。
方針：境界単体の定値性で二つの端点の図式へ戻す。
規約：全パラメータ・全次数の等式。
使われ方：相対境界の輸送円柱とその底の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：元の区間境界の射は、その二端点から作る境界図式と厳密に一致。
方針：各境界単体を定値な端点と同定する。
規約：射の値を選び直さない。使われ方：全境界円柱の端点による照合。 -/
lemma intervalBoundaryDiagram_eta {A X : SSet.{u}}
    (h : (boundary 1 : SSet.{u}) ⊗ A ⟶ X) :
    h = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ≫ h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ≫ h) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change h.app _ (s, x) =
    (if s.val 0 = 0 then h.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A).app _ x)
    else h.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A).app _ x))
  split_ifs with hs
  · apply congrArg (h.app _)
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    apply stdSimplex.ext
    intro j
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j).trans hs
  · have hs' : s.val 0 = 1 := by
      apply Fin.ext
      change (s.val 0).val = 1
      have h := (s.val 0).isLt
      have h' : (s.val 0).val ≠ 0 := fun h ↦ hs (Fin.ext h)
      omega
    apply congrArg (h.app _)
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    apply stdSimplex.ext
    intro j
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.boundaryOne_simplex_constant s j).trans hs'

/-- 概要：区間境界上の二射は指定二端点で一致すれば一致する。
方針：両者を元の二端点の図式へ戻す。
規約：全パラメータ。使われ方：輸送円柱の貼り合わせと底の照合。 -/
lemma intervalBoundary_hom_ext {A X : SSet.{u}}
    {f g : (boundary 1 : SSet.{u}) ⊗ A ⟶ X}
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ≫ g)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ≫ g) : f = g := by
  rw [intervalBoundaryDiagram_eta f, intervalBoundaryDiagram_eta g, h₀, h₁]

/-- 概要：区間境界の全円柱も二端点上の全円柱で厳密に決まる。
方針：時間をパラメータへ移し、区間境界の二端点の一意性を使う。
規約：時間の全単体を保持。使われ方：相対境界円柱の共通部分の一致。 -/
lemma intervalBoundaryCylinder_hom_ext {A X : SSet.{u}}
    {R S : ((boundary 1 : SSet.{u}) ⊗ A) ⊗ (Δ[1] : SSet.{u}) ⟶ X}
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫ R =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 0 A ▷ (Δ[1] : SSet.{u})) ≫ S)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫ R =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint 1 A ▷ (Δ[1] : SSet.{u})) ≫ S) : R = S := by
  apply (cancel_epi (α_ (boundary 1 : SSet.{u}) A (Δ[1] : SSet.{u})).inv).1
  apply intervalBoundary_hom_ext
  · exact h₀
  · exact h₁

end SerrePositivity.InfinityCategories.Project.FilteredExchange
