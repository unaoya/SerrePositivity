module

public import SerrePositivity.KST.NonConnective.DGSwindleInputIso
public import SerrePositivity.KST.NonConnective.DGFixedKAction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：元の実 dg swindle の、K-S• の同じ固定 BF K への作用。
方針：元の native Hom の実辺を固定入力へ持ち上げ、固定 K に写して全整数 π で読む。
規約：K の加法性・消滅はまだ結論せず、同じ二つの実自己射の作用を照合する。
使われ方：BGT Lem. 9.4 の swindle 消去の同型側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 同じ cone の id ⊕ T を、元の固定 dg 入力の通常射として保持する。 -/
def dgKappaSwindleInputMap : dgKappaConeKInput R D I ⟶ dgKappaConeKInput R D I :=
  ULift.up (dgKappaSwindleSource R D I)

/-- 同じ cone の T を、元の固定 dg 入力の通常射として保持する。 -/
def dgKappaCountableInputMap : dgKappaConeKInput R D I ⟶ dgKappaConeKInput R D I :=
  ULift.up (dgKappaConeCountableSum R D I)

/-- 固定入力の同じ全 native Kan Hom の、元の swindle 同型の実辺。 -/
def dgKappaSwindleFixedInputHomEdge :
    (SimplicialCategory.sHom (dgKappaConeKInput R D I) (dgKappaConeKInput R D I)).Edge
      (SimplicialCategory.homEquiv' _ _ (dgKappaSwindleInputMap R D I))
      (SimplicialCategory.homEquiv' _ _ (dgKappaCountableInputMap R D I)) := by
  rw [dgFixedInputVertex, dgFixedInputVertex]
  change ((SSet.uliftFunctor.{u + 1, max (u + 1) v}).obj
    (dgFunctorNativeMappingSpace R (DGKappaCone R D I) (DGKappaCone R D I))).Edge
      (ULift.up (dgFunctorNativeMappingVertex R _ _ (dgKappaSwindleSource R D I)))
      (ULift.up (dgFunctorNativeMappingVertex R _ _ (dgKappaConeCountableSum R D I)))
  exact SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge (dgKappaSwindleNativeInputEdge R D I).toTruncated)

/-- 元の入力の同じ二つの辺は、固定入力 ∞ 圏の h で等しい。 -/
lemma dgKappaSwindleInput_hom_eq :
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSwindleInputMap R D I)).toTruncated =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaCountableInputMap R D I)).toTruncated := by
  let e := dgKappaSwindleFixedInputHomEdge R D I
  let : IsIso (Truncated.HomotopyCategory.homMk e.toTruncated) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      (SimplicialCategory.sHom (dgKappaConeKInput R D I) (dgKappaConeKInput R D I))) _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_homMk_eq_of_enrichedVertexIso
    (asIso (Truncated.HomotopyCategory.homMk e.toTruncated))

local instance dgSwindleFixedKSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- 元の固定 BF K の同じ二つの実自己射は、全整数 π に同じ作用を与える。 -/
theorem dgKappaSwindleFixedK_pi (j : ℤ) :
    OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R (dgKappaSwindleInputMap R D I)) j =
      OmegaSpectrum.homotopyMap (dgKInputSpectrumMap R (dgKappaCountableInputMap R D I)) j := by
  exact dgFixedKAction_eq R _
    (dgKappaSwindleInputMap R D I) (dgKappaCountableInputMap R D I)
    (dgKappaSwindleInput_hom_eq R D I) j

end SerrePositivity.KST.NonConnective
