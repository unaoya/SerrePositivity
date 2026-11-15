module

public import SerrePositivity.InfinityCategories.Sheaves.SheafificationReflection
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：通常 site の関手の元の nerve による、全前層関手圏の再添字を固定する。
方針：同じ反対関手・nerve・持ち上げを使い、site 同値では前合成の同値性を適用する。
使われ方：HTT 1.2.7.3、Kerodon §4.5.1（Tag 01DQ）の前層圏の同値。
規約：このファイルは前層圏の比較。被覆位相と層の比較は後続で証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C D B : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory B]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 通常の関手の元の反対 nerve による形状の写像。 -/
def siteShapeMap (f : C ⥤ D) : presheafShape C ⟶ presheafShape D :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap f.op)

/-- 同じ形状の写像による前層の再添字。 -/
def reindexPresheaf (f : C ⥤ D) (F : Presheaf D E) : Presheaf C E :=
  siteShapeMap f ≫ F

/-- 射・全高次単体も含む同じ再添字関手。 -/
def reindexPresheafFunctor (f : C ⥤ D) : PresheafCat D E ⟶ PresheafCat C E :=
  (pre (siteShapeMap f)).app E

/-- 通常の site 同値の元の形状の写像は準圏の同値。 -/
lemma siteShapeMap_isQCatEquivalence (e : C ≌ D) :
    IsQCatEquivalence (siteShapeMap e.functor) := by
  have h := (nerveQCatEquivalence e.op).isQCatEquivalence
  exact SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1} h

/-- site 同値に沿う再添字は、元の全前層圏の同値を与える。 -/
lemma reindexPresheafFunctor_isQCatEquivalence (e : C ≌ D) :
    IsQCatEquivalence (reindexPresheafFunctor (E := E) e.functor) :=
  (siteShapeMap_isQCatEquivalence e).isPrecompositionEquivalence E

end SerrePositivity.InfinityCategories.Sheaves
