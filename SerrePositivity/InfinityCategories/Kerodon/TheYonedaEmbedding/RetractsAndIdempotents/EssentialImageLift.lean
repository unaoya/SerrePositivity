module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：元の充満忠実な関手を、その全ての同型像の全部分圏への同値へ因子化する。
方針：元の頂点同型を所属条件とし、包含の充満忠実性で内部の同型を回収する。
規約：元の包含後に元の全関手を厳密に回収する。
使われ方：HTT 5.1.4.8 の本質像内に値を持つ全関手の回収。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の関手の同型像の全頂点で張られた、元の標的の全部分複体。 -/
def fullEssentialImage {X Y : SSet.{u}} (f : X ⟶ Y) : Y.Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y
    (fun y ↦ ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x) y))

/-- 元の quasicategory の全本質像は、元の全部分 quasicategory。 -/
instance fullEssentialImage_quasicategory {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) :
    Quasicategory (fullEssentialImage f).toSSet :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y
    (fun y ↦ ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x) y)) : SSet.{u}))

/-- 元の全関手を、その同型像の全部分圏へ厳密に因子化する。 -/
def essentialImageLift {X Y : SSet.{u}} (f : X ⟶ Y) : X ⟶ fullEssentialImage f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ f (fun x ↦ ⟨x, ⟨Iso.refl _⟩⟩)

/-- 本質像の元の包含後に、元の全関手そのものを厳密に回収する。 -/
lemma essentialImageLift_inclusion {X Y : SSet.{u}} (f : X ⟶ Y) :
    essentialImageLift f ≫ (fullEssentialImage f).ι = f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の充満忠実な関手の、本質像への同じ持ち上げは充満忠実。 -/
lemma essentialImageLift_isFullyFaithful {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (essentialImageLift f) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (fullEssentialImage f).ι :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y _
  exact hi.cancel_right ((essentialImageLift_inclusion f).symm ▸ hf)

/-- 元の全関手の同型像への同じ持ち上げは、本質的全射。 -/
lemma essentialImageLift_isEssentiallySurjective {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (essentialImageLift f) := by
  intro y
  obtain ⟨x, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
  refine ⟨x, ⟨(_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y _).preimageVertexIso ?_⟩⟩
  exact e

/-- 元の充満忠実な関手の本質像への同じ持ち上げは、実際の ∞ 圏同値。 -/
lemma essentialImageLift_isQCatEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (essentialImageLift f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective (essentialImageLift f)
    (essentialImageLift_isFullyFaithful f hf) (essentialImageLift_isEssentiallySurjective f)

/-- 元の本質像への持ち上げを順方向として保持する同値。 -/
def essentialImageEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X (fullEssentialImage f) :=
  (essentialImageLift_isQCatEquivalence f hf).choose

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
