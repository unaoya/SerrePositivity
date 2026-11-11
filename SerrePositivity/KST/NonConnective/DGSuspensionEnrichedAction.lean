module
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeActionInput
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-!
概要：採用した懸垂作用の供給路を、元の全 Hom 族から固定 S 作用へ接続する。
方針：同じ対象関数の厳密 SSet 豊穣自己関手を作り、coherentNerveMap を取る。
規約：全 Hom 族・豊穣単位合成則・元の dg 射との照合に条件付き。D の厳密関手性を主張しない。
使われ方：DGSuspensionNativeActionInput の採用（03:55）供給路。入力の存在は未供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (H : ∀ A B : PerfDGInput.{u, max (u + 1) v} R,
    (A ⟶[SSet.{max (u + 1) v}] B) ⟶
      (dgKappaSuspensionKInput R A (s A).cone ⟶[SSet.{max (u + 1) v}]
        dgKappaSuspensionKInput R B (s B).cone))
  (hid : ∀ A, eId SSet A ≫ H A A = eId SSet (dgKappaSuspensionKInput R A (s A).cone))
  (hcomp : ∀ A B C, eComp SSet A B C ≫ H A C = (H A B ⊗ₘ H B C) ≫
    eComp SSet (dgKappaSuspensionKInput R A (s A).cone)
      (dgKappaSuspensionKInput R B (s B).cone) (dgKappaSuspensionKInput R C (s C).cone))

/-- 明示全 Hom 族と豊穣単位合成則に条件付きの、同じ実懸垂を対象とする厳密豊穣自己関手。 -/
def dgSuspensionEnrichedSelfFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, max (u + 1) v} R)
      (PerfDGInput.{u, max (u + 1) v} R) where
  obj A := dgKappaSuspensionKInput R A (s A).cone
  map := H
  map_id := hid
  map_comp := hcomp

/-- 明示全 Hom 族・豊穣則・元の実 dg 射との照合に条件付きで、採用した全高次作用を供給する。 -/
def DGSuspensionNativeActionInput.ofEnrichedHom
    (d : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
      DGKappaSuspensionMapData R A B (s A).cone (s B).cone)
    (hedge : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
      eHomEquiv SSet f ≫ H A B =
        eHomEquiv SSet (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (d f))) :
    DGSuspensionNativeActionInput R s where
  map := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgSuspensionEnrichedSelfFunctor R s H hid hcomp)
  vertex A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ A
  data := d
  edge f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv _ f _ (hedge f)

end SerrePositivity.KST.NonConnective
