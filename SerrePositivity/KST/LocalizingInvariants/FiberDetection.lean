module

public import SerrePositivity.KST.Spectra.HomotopyFiberVanishing
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection

/-!
概要：実 fiber の全整数ホモトピー群の消滅による同値検出。
方針：長完全列の二箇所から元の射の単射・全射を得て、Sp-5 d1 を適用する。
規約：fiber 群の消滅を追加公理にしない。使われ方：局所化不変量の基本判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants

namespace FiberDetection

/-- 実 homotopy fiber の全整数次数の群が自明なら、元の射は全整数 π 同型。 -/
theorem piIsomorphism_of_fiberGroups {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (h : ∀ j : ℤ, Subsingleton (homotopyGroup (homotopyFiber f) j)) : PiIsomorphism f := by
  have hinj (j : ℤ) : Function.Injective (homotopyMap f j) := by
    apply (injective_iff_map_eq_one _).2
    intro a ha
    obtain ⟨b, hb⟩ := (homotopy_exact_fiber_total f j a).1 ha
    have hb₀ : b = 1 := (h j).elim b 1
    rw [← hb, hb₀, map_one]
  have hsurj (j : ℤ) : Function.Surjective (homotopyMap f (j + 1)) := by
    intro a
    apply (homotopy_exact_total_base f j a).1
    exact (h j).elim _ _
  intro j
  refine ⟨hinj j, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k + 1 = j := ⟨j - 1, by omega⟩
  subst j
  exact hsurj k

/-- 全整数 π 同型と実 fiber の全整数群の消滅は同値。 -/
theorem piIsomorphism_iff_fiberGroups {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    PiIsomorphism f ↔ ∀ j : ℤ, Subsingleton (homotopyGroup (homotopyFiber f) j) :=
  ⟨fun h ↦ h.homotopyFiberGroup_subsingleton, piIsomorphism_of_fiberGroups f⟩

local instance fiberDetectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- fiber の全整数群の消滅は、元の Sp の辺の可逆性を検出する。 -/
theorem isInvertible_of_fiberGroups {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (h : ∀ j : ℤ, Subsingleton (homotopyGroup (homotopyFiber f) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) :=
  isInvertible_of_piIsomorphism f (piIsomorphism_of_fiberGroups f h)

end FiberDetection
end SerrePositivity.KST.LocalizingInvariants
