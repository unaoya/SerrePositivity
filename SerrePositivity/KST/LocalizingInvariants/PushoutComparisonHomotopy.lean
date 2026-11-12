module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquarePrismGluing
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyPrecompVertex
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
概要：共有境界で一致する実比較円柱を、貼合せ全図式の一つの可逆比較へ戻す。
方針：区間との積が保つ pushout の普遍性で貼り、頂点の共同全射性で可逆性を検査する。
規約：二つの制限を実円柱そのものの等式として保ち、比較辺を選び直さない。
使われ方：c5 の元の有限図式と回収済み尾部の全境界比較の組立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {S A B P X : SSet.{u}} {a : S ⟶ A} {b : S ⟶ B}
  {l : A ⟶ P} {r : B ⟶ P} (s : IsPushout a b l r) {F G : P ⟶ X}
  (J : SSet.Homotopy (l ≫ F) (l ≫ G))
  (K : SSet.Homotopy (r ≫ F) (r ≫ G))
  (h : (a ▷ (Δ[1] : SSet.{u})) ≫ J.h = (b ▷ (Δ[1] : SSet.{u})) ≫ K.h)

/-- 共有部分の実比較が一致する二つの全比較を、一つの全円柱に貼る。 -/
def pushoutComparisonHomotopy : SSet.Homotopy F G where
  h := (s.map (tensorRight (Δ[1] : SSet.{u}))).desc J.h K.h h
  h₀ := by
    apply s.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, IsPushout.inl_desc]
      exact J.h₀
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, IsPushout.inr_desc]
      exact K.h₀
  h₁ := by
    apply s.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, IsPushout.inl_desc]
      exact J.h₁
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, IsPushout.inr_desc]
      exact K.h₁
  rel := by
    ext n t
    exact False.elim t.1.2

lemma pushoutComparisonHomotopy_left :
    (l ▷ (Δ[1] : SSet.{u})) ≫ (pushoutComparisonHomotopy s J K h).h = J.h :=
  (s.map (tensorRight (Δ[1] : SSet.{u}))).inl_desc _ _ _

lemma pushoutComparisonHomotopy_right :
    (r ▷ (Δ[1] : SSet.{u})) ≫ (pushoutComparisonHomotopy s J K h).h = K.h :=
  (s.map (tensorRight (Δ[1] : SSet.{u}))).inr_desc _ _ _

/-- 貼合せ全比較は、元の両比較が各頂点で可逆なら各頂点で可逆。 -/
lemma pushoutComparisonHomotopy_isInvertible [Quasicategory X]
    (hJ : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).toTruncated)
    (hK : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (pushoutComparisonHomotopy s J K h)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro x
  have hs := s.map ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌))
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := Types.eq_or_eq_of_isPushout hs x
  · have he := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge
      (pushoutComparisonHomotopy s J K h) l x
    have hh : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (pushoutComparisonHomotopy s J K h) l).h = J.h :=
      pushoutComparisonHomotopy_left s J K h
    have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (pushoutComparisonHomotopy s J K h) l) x).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).edge := by
      exact congrArg (fun f => f.app (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj A) x).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hh
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (he.symm.trans hv)).mpr (hJ x)
  · have he := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge
      (pushoutComparisonHomotopy s J K h) r x
    have hh : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (pushoutComparisonHomotopy s J K h) r).h = K.h :=
      pushoutComparisonHomotopy_right s J K h
    have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (pushoutComparisonHomotopy s J K h) r) x).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).edge := by
      exact congrArg (fun f => f.app (Opposite.op ⦋1⦌)
        ((Truncated.Edge.id (X := (truncation 2).obj B) x).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hh
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (he.symm.trans hv)).mpr (hK x)

end SerrePositivity.KST.LocalizingInvariants
