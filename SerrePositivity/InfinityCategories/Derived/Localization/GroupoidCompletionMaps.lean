module

public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletion
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：全辺局所化の実関手性と、trivial Kan fibration に沿う亜群化の不変性。
方針：元の射を普遍性で下ろし、逆と両合成の同型も同じ普遍性で下ろす。
規約：元の単体集合の quasicategory 性は不要。
使われ方：三角補完を記憶した分数模型から補完を忘れる際の実同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def groupoidCompletionMapOf {X Y : SSet.{u}} (f : X ⟶ Y) :
    groupoidCompletion X ⟶ groupoidCompletion Y :=
  localizationDescend _ _ (groupoidCompletion_isLocalization X)
    (f ≫ groupoidCompletionMap Y) (invertsAllEdges_toKan _)

def groupoidCompletionMapOfIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    FunctorIso (groupoidCompletionMap X ≫ groupoidCompletionMapOf f)
      (f ≫ groupoidCompletionMap Y) :=
  localizationDescendIso _ _ (groupoidCompletion_isLocalization X)
    (f ≫ groupoidCompletionMap Y) (invertsAllEdges_toKan _)

def groupoidCompletionMapOf_compIso {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    FunctorIso (groupoidCompletionMapOf f ≫ groupoidCompletionMapOf g)
      (groupoidCompletionMapOf (f ≫ g)) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  have h := FunctorIso.postcomp (groupoidCompletionMapOfIso f) (groupoidCompletionMapOf g) ≪≫
    FunctorIso.precomp (groupoidCompletionMapOfIso g) f ≪≫
    (groupoidCompletionMapOfIso (f ≫ g)).symm
  simpa only [Category.assoc] using h

def groupoidCompletionMapOf_idIso (X : SSet.{u}) :
    FunctorIso (groupoidCompletionMapOf (𝟙 X)) (𝟙 (groupoidCompletion X)) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  simpa only [Category.id_comp, Category.comp_id] using groupoidCompletionMapOfIso (𝟙 X)

def groupoidCompletionMapOf_functorIso {X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : FunctorIso f g) : FunctorIso (groupoidCompletionMapOf f) (groupoidCompletionMapOf g) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  exact groupoidCompletionMapOfIso f ≪≫ FunctorIso.postcomp e (groupoidCompletionMap Y) ≪≫
    (groupoidCompletionMapOfIso g).symm

def groupoidCompletionEquivalenceOfTrivialKanFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] : QCatEquivalence (groupoidCompletion X) (groupoidCompletion Y) := by
  let s := Classical.choose (trivialKanFibration_exists_section p)
  have hs : s ≫ p = 𝟙 Y := Classical.choose_spec (trivialKanFibration_exists_section p)
  have hps : FunctorIso (p ≫ s) (𝟙 X) :=
    functorIsoOfTrivialKanFibration p (p ≫ s) (𝟙 X) (by
      simp only [Category.assoc, hs, Category.comp_id, Category.id_comp])
  refine
    { hom := groupoidCompletionMapOf p
      inv := groupoidCompletionMapOf s
      homInvIso := groupoidCompletionMapOf_compIso p s ≪≫
        groupoidCompletionMapOf_functorIso hps ≪≫ groupoidCompletionMapOf_idIso X
      invHomIso := ?_ }
  have e := groupoidCompletionMapOf_compIso s p
  rw [hs] at e
  exact e ≪≫ groupoidCompletionMapOf_idIso Y

/-- 全関手同値の逆と両比較を、同じ亜群化の普遍性で下ろす。 -/
lemma groupoidCompletionMapOf_isQCatEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsQCatEquivalence f) :
    IsQCatEquivalence (groupoidCompletionMapOf f) := by
  obtain ⟨g, ⟨hfg⟩, ⟨hgf⟩⟩ := hf
  exact ⟨groupoidCompletionMapOf g,
    ⟨groupoidCompletionMapOf_compIso f g ≪≫ groupoidCompletionMapOf_functorIso hfg ≪≫
      groupoidCompletionMapOf_idIso X⟩,
    ⟨groupoidCompletionMapOf_compIso g f ≪≫ groupoidCompletionMapOf_functorIso hgf ≪≫
      groupoidCompletionMapOf_idIso Y⟩⟩

lemma groupoidCompletionMapOf_trivialKanFibration_isEquivalence {X Y : SSet.{u}} (p : X ⟶ Y)
    [TrivialKanFibration p] : IsSimplicialHomotopyEquivalence (groupoidCompletionMapOf p) :=
  (groupoidCompletionEquivalenceOfTrivialKanFibration p).isQCatEquivalence
    |>.isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
