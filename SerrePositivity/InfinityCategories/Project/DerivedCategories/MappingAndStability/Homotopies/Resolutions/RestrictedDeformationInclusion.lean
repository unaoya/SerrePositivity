module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.RestrictedDeformationHomotopy
/-!
概要：頂点全部分圏上へ制限した元の変形円柱の実包含後を計算する。
方針：同じ全円柱写像の標準持ち上げの射影式を使う。
規約：全時刻・全面・退化を含む写像を保持。使われ方：K-flat の変形比較の経路照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalCategory
open scoped _root_.Simplicial
/-- 同じ制限変形円柱に実包含を続けると、元の円柱の同じ入力制限へ厳密に戻る。 -/
lemma deformationRestrictedHomotopy_ι {X D : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (L : X ⟶ D) (I : D ⟶ X)
    (hI : ∀ x, P (I.app (Opposite.op ⦋0⦌) x))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X)) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.deformationRestrictedHomotopy P L I hI H).h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).h := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.deformationRestrictedHomotopy
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.fullSubcomplexHomotopyLift_ι _ _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
