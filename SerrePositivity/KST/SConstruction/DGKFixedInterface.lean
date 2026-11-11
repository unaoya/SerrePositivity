module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGExactInfinityFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMoritaInfinity
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFOrdinaryNaturality

/-! # 厳密 dg 入力の ν・K 固定界面
概要：同じ入力 ∞ 圏 S 上の安定値 ν とスペクトル値 K を固定する。
方針：構成済みの二つの厳密豊穣関手の coherent nerve をそのまま使う。
規約：一般の安定 ∞ 圏上の K は定義しない。使われ方：K-F と Sp の相対版への入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

private lemma stableHom_inclusion
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{w}} (f : C ⟶ D) :
    (eHomEquiv SSet f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{w})).ι) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D).ι =
          MonoidalClosed.curry' f.hom := by
  have h : eHomEquiv SSet f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors C D : SSet.{w})).ι =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv f := by
    apply (SSet.unitHomEquiv _).injective
    rfl
  rw [h]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι f

/-- 固定始域 S は、全 native Hom を持つ厳密 dg 入力の ∞ 圏。 -/
abbrev dgKInputInfinity : SSet.{max (u + 1) v + 1} := perfDGInputInfinity.{u, v} A

/-- 同じ S 上で既に構成した安定 ∞ 圏値関手 ν。 -/
def dgKInputNu :
    dgKInputInfinity.{u, v} A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} :=
  presentedPerfectDGExactInfinityFunctor A

/-- 同じ S 上で既に構成したスペクトル値関手 K。 -/
def dgKInputK : dgKInputInfinity.{u, v} A ⟶ Sp.{max (u + 1) v} :=
  presentedPerfectDGBFInfinityFunctor A

/-- ν の対象別の実安定値。 -/
abbrev dgKInputStableValue (P : PerfDGInput.{u, v} A) :=
  presentedPerfectDGStableCategory A P

/-- ν の各頂点は元の実安定値の頂点そのもの。 -/
lemma dgKInputNu_vertex (P : PerfDGInput.{u, v} A) :
    (dgKInputNu A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue A P) :=
  presentedPerfectDGExactInfinityFunctor_vertex A P

/-- ν の同じ辺を、元の全 Hom 作用から通常射として回収する。 -/
def dgKInputNuMap {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    presentedPerfectDGStableQCat A P ⟶ presentedPerfectDGStableQCat A Q :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap (presentedPerfectDGEnrichedExactFunctor A) f

/-- ν の元の全 Hom 作用は、同じ厳密 dg 延長の完全射を回収する。 -/
lemma dgKInputNuMap_eq {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    dgKInputNuMap A f = presentedPerfectDGExactMap A f := by
  apply (eHomEquiv SSet).injective
  refine (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_hom
    (presentedPerfectDGEnrichedExactFunctor A) f).trans ?_
  apply (cancel_mono ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
      (presentedPerfectDGStableCategory A P) (presentedPerfectDGStableCategory A Q) :
        SSet.{max (u + 1) v})).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
          (presentedPerfectDGStableCategory A P) (presentedPerfectDGStableCategory A Q)).ι)).1
  have h := presentedPerfectDGExactCoreFamilyMap_inclusion A P Q
  have hr := stableHom_inclusion
    (show presentedPerfectDGStableQCat A P ⟶ presentedPerfectDGStableQCat A Q from
      presentedPerfectDGExactMap A f)
  change (eHomEquiv SSet f ≫ presentedPerfectDGExactCoreFamilyMap A P Q) ≫ _ = _
  erw [Category.assoc, ← Category.assoc (presentedPerfectDGExactCoreFamilyMap A P Q), h]
  exact (presentedPerfectDGNativeFamilyMap_fixed A P Q f.down).trans hr.symm

/-- ν の一単体の像は元の全 Hom 作用による同じ辺。 -/
lemma dgKInputNu_edge {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    (dgKInputNu A).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputNuMap A f)).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv _ f _
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_hom _ f).symm

/-- 固定 K の実対象は、元の S• 境界商から構成した同じ BF Ω スペクトル。 -/
abbrev dgKInputSpectrum (P : PerfDGInput.{u, v} A) := presentedPerfectDGBFOmegaSpectrum A P

/-- 固定 K の実射は、元の厳密豊穣 BF 射。 -/
abbrev dgKInputSpectrumMap {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :=
  presentedPerfectDGBFMap A f

/-- 同じ実 BF の単体的圏を固定界面でも使う。 -/
local instance fixedSpectrum_simplicialCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

/-- K の各頂点は、同じ S• BF スペクトルの頂点そのもの。 -/
lemma dgKInputK_vertex (P : PerfDGInput.{u, v} A) :
    (dgKInputK A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum A P) :=
  presentedPerfectDGBFInfinityFunctor_vertex A P

/-- K の各辺は、同じ S• BF スペクトルの元の射そのもの。 -/
lemma dgKInputK_edge {P Q : PerfDGInput.{u, v} A} (f : P ⟶ Q) :
    (dgKInputK A).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap A f)).edge :=
  presentedPerfectDGBFInfinityFunctor_edge A f

end SerrePositivity.KST.SConstruction
