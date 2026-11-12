module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowIsoRealization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-!
概要：像内の両端を持つ実辺の持上げと対象の本質的全射性から、矢印図式を持ち上げる。
方針：対象の同型で辺を移し、実四角形の関手同型を経由して元の辺へ戻す。
規約：標的は関手 ∞ 圏であり h 圏の通常矢印圏ではない。
使われ方：一般 Tamme 商への矢印図式の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma arrowMap_isEssentiallySurjective {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective F)
    (hA : ∀ {x y : X _⦋0⦌},
      (f : Truncated.Edge (X := (truncation 2).obj Q)
        (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)) →
      ∃ g : (Δ[1] : SSet.{u}) ⟶ X,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ F) (SSet.yonedaEquiv.symm f.edge))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((ihom (Δ[1] : SSet.{u})).map F) := by
  intro v
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] : SSet.{u}) Q).surjective v
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv f)
  obtain ⟨x, ⟨a⟩⟩ := hF (Q.δ 1 (SSet.yonedaEquiv f))
  obtain ⟨y, ⟨b⟩⟩ := hF (Q.δ 0 (SSet.yonedaEquiv f))
  obtain ⟨t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
    (a.hom ≫ SSet.Truncated.HomotopyCategory.homMk e ≫ b.inv)
  have hc : SSet.Truncated.HomotopyCategory.homMk t ≫ b.hom =
      a.hom ≫ SSet.Truncated.HomotopyCategory.homMk e := by
    rw [ht]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨c⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrowFunctorIso_of_vertexIso_comm t e a b hc
  obtain ⟨g, ⟨d⟩⟩ := hA t
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g, ⟨?_⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ F) f
  have h := d ≪≫ c
  have he : SSet.yonedaEquiv.symm e.edge = f := SSet.yonedaEquiv.symm_apply_apply f
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowMap_isEssentiallySurjective := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.arrowMap_isEssentiallySurjective
