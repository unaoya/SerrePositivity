module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeSectionsValueMap
public import SerrePositivity.InfinityCategories.F1.Coherent.SectionsConeIdentity
public import SerrePositivity.InfinityCategories.F1.Universe.FunctorSpaceVertex

/-!
概要：実現した全切断の錐の、元の fiber から全切断への実際の射の同値性を示す。
方針：指定恒等射の比較を内部 Hom の宇宙同型で戻し、値の正規化の同値を消去する。
規約：元の図式・実現した錐・同じ標準比較射を保持する。
使われ方：全 Hom 作用の後合成の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
local instance : KanComplex (HomotopyLimits.simplicialSections (leftUnstraighteningProjection F)) :=
  HomotopyLimits.simplicialSections_kanComplex (leftUnstraighteningProjection F)
local instance : KanComplex
    (HomotopyLimits.simplicialSections (smallLeftUnstraighteningProjection F)) :=
  HomotopyLimits.simplicialSections_kanComplex (smallLeftUnstraighteningProjection F)

/-- 元の全切断の値を同一視するだけの恒等射との、実際の全切断写像の比較。 -/
def coherentSectionsConeValueIdentityIso :
    FunctorIso (coneSectionsValueMapAt F (coherentDiagramSectionsCone F)
      (coherentSpaceSectionsVertex F) (coherentDiagramSectionsCone_vertex F))
      ((SSet.uliftFunctor.{u + 1, u}).map (coherentSpaceSectionsIdentity F)) := by
  have e := (coherentSectionsConeIdentityIso F).map
    (uliftFunctorSpaceIso (spaceInfinityObject (coherentSpaceSectionsVertex F)).obj
      (coherentSpaceSectionsObject F).obj).hom
  rw [coneSectionsValueMapAt_smallComparison, uliftFunctorSpaceIso_hom_vertex] at e
  exact e

/-- 値を正規化した全切断の実際の射は同値。 -/
lemma coherentSectionsConeValueMap_isQCatEquivalence :
    IsQCatEquivalence (coneSectionsValueMapAt F (coherentDiagramSectionsCone F)
      (coherentSpaceSectionsVertex F) (coherentDiagramSectionsCone_vertex F)) := by
  have h := (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
    (eqToIso (coherentSpaceSectionsVertex_object F)))).isQCatEquivalence
  exact h.ofFunctorIso (coherentSectionsConeValueIdentityIso F).symm

/-- 同じ錐の元の pointed fiber から全切断への標準写像自体が同値。 -/
lemma coherentSectionsConeMapAt_isQCatEquivalence :
    IsQCatEquivalence (coneSectionsMapAt (coherentDiagramSectionsCone F)
      (coherentSpaceSectionsVertex F) (coherentDiagramSectionsCone_vertex F)) := by
  have h := coherentSectionsConeValueMap_isQCatEquivalence F
  change IsQCatEquivalence ((pointedSpaceFiberValueEquivalence _).symm.hom ≫
    coneSectionsMapAt _ _ _ ≫ (smallUnstraighteningSectionsIso F).inv) at h
  have hs := (qCatEquivalenceOfIso (smallUnstraighteningSectionsIso F).symm).isQCatEquivalence
  have hv :=
    (pointedSpaceFiberValueEquivalence (coherentSpaceSectionsVertex F)).symm.isQCatEquivalence
  have h' := hv.cancel_left h
  exact hs.cancel_right h'

end SerrePositivity.InfinityCategories
