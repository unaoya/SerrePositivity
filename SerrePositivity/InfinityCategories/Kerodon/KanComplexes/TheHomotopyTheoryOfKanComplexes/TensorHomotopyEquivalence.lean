module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanTensorAdjunction

/-!
概要：同じ時間の二つのホモトピーを対にし、直積のホモトピー同値を構成する。
方針：元の円柱の射を二射影で組み、逆射の両合成も同じ円柱で比較する。
規約：一般の単体集合で成立。使われ方：二つの普遍 fiber の比較を同時に扱う。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan

/-- 二つのホモトピーを、同じ時間を持つ直積へのホモトピーにする。 -/
def pairedSimplicialHomotopy {A X Y : SSet.{u}} {f f' : A ⟶ X} {g g' : A ⟶ Y}
    (H : SSet.Homotopy f f') (J : SSet.Homotopy g g') :
    SSet.Homotopy (lift f g) (lift f' g') where
  h := lift H.h J.h
  h₀ := by rw [comp_lift, H.h₀, J.h₀]; rfl
  h₁ := by rw [comp_lift, H.h₁, J.h₁]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- Kan 標的への二つの関手同型は、同じ始域から直積への関手同型を与える。 -/
def pairedKanFunctorIso {A X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f f' : A ⟶ X} {g g' : A ⟶ Y} (H : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f') (J : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g g') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (lift f g) (lift f' g') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
    (pairedSimplicialHomotopy H.simplicialHomotopy J.simplicialHomotopy)

/-- 元の二つの逆射の直積は、元の直積射のホモトピー逆。 -/
lemma tensor_isSimplicialHomotopyEquivalence {A B X Y : SSet.{u}}
    {f : A ⟶ X} {g : B ⟶ Y}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ⊗ₘ g) := by
  obtain ⟨f', ⟨H⟩, ⟨J⟩⟩ := hf
  obtain ⟨g', ⟨P⟩, ⟨Q⟩⟩ := hg
  refine ⟨f' ⊗ₘ g', ?_, ?_⟩
  · have T := pairedSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (fst A B)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp P (snd A B))
    have hs : lift (fst A B ≫ f ≫ f') (snd A B ≫ g ≫ g') =
        (f ⊗ₘ g) ≫ (f' ⊗ₘ g') := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have ht : lift (fst A B ≫ 𝟙 A) (snd A B ≫ 𝟙 B) = 𝟙 (A ⊗ B) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hs, ht] at T
    exact ⟨T⟩
  · have T := pairedSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp J (fst X Y)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Q (snd X Y))
    have hs : lift (fst X Y ≫ f' ≫ f) (snd X Y ≫ g' ≫ g) =
        (f' ⊗ₘ g') ≫ (f ⊗ₘ g) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have ht : lift (fst X Y ≫ 𝟙 X) (snd X Y ≫ 𝟙 Y) = 𝟙 (X ⊗ Y) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hs, ht] at T
    exact ⟨T⟩

/-- Kan 複体の二つの同値の直積は、指定した同じ直積射の同値。 -/
lemma tensor_isQCatEquivalence {A B X Y : SSet.{u}}
    [KanComplex A] [KanComplex B] [KanComplex X] [KanComplex Y]
    {f : A ⟶ X} {g : B ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (f ⊗ₘ g) :=
  (tensor_isSimplicialHomotopyEquivalence hf.isSimplicialHomotopyEquivalence
    hg.isSimplicialHomotopyEquivalence).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
