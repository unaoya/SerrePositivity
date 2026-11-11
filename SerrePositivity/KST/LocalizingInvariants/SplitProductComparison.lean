module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumMultiplicationGroups
public import SerrePositivity.KST.LocalizingInvariants.CoherentSplitFiberGroups
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：coherent な切断を持つ BF fiber 列の、元の二項積からの実比較同値。
方針：包含と切断を構成済みの積の射で合わせ、長完全列の分裂で整数 π 同型性を示す。
規約：射影との h Sp での整合性は後続の補正で証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SplitProduct

local instance splitProductSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (s : Y ⟶ X)

/-- 実 fiber と底の実二項積から、元の全空間への実 BF 射。 -/
def comparison : Binary.obj (homotopyFiber f) Y ⟶ X :=
  Binary.lift (Binary.fst (homotopyFiber f) Y ≫ homotopyFiberInclusion f)
    (Binary.snd (homotopyFiber f) Y ≫ s) ≫ Multiplication.map X

lemma comparison_map (j : ℤ) : homotopyMap (comparison f s) j =
    (SplitFiber.groupMap f s j).comp (Binary.groupProjection (homotopyFiber f) Y j) := by
  ext a
  change homotopyMap (Binary.lift _ _ ≫ Multiplication.map X) j a = _
  rw [Multiplication.pair_apply, homotopyMap_comp, homotopyMap_comp]
  rfl

variable (hs : SpectrumHo.hom s ≫ SpectrumHo.hom f = 𝟙 (SpectrumHo.obj Y))
include hs

lemma comparison_piIsomorphism : PiIsomorphism (comparison f s) := by
  intro j
  rw [comparison_map]
  exact (CoherentSplitFiber.groupMap_bijective f s hs j).comp
    ⟨Binary.groupProjection_injective _ _ j, Binary.groupProjection_surjective _ _ j⟩

/-- 分裂比較は、元の Sp の辺として可逆である。 -/
lemma comparison_isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (comparison f s)) :=
  isInvertible_of_piIsomorphism (comparison f s) (comparison_piIsomorphism f s hs)

def productVertexIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (homotopyFiber f) Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) := by
  haveI : IsIso (SpectrumHo.hom (comparison f s)) := comparison_isInvertible f s hs
  exact asIso (SpectrumHo.hom (comparison f s))

end SerrePositivity.KST.LocalizingInvariants.SplitProduct
