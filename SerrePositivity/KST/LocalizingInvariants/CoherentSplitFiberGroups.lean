module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyClass
public import SerrePositivity.KST.LocalizingInvariants.SplitFiberGroups

/-!
概要：Sp のホモトピー圏で切断を持つ BF fiber 列の全整数 π の分裂。
方針：切断の類の等式を π の等式へ移し、元の長完全列を使う。
規約：BF 射の厳密な切断は要求しない。Sp の積同値はなお別工程。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.CoherentSplitFiber

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
  (hs : SpectrumHo.hom s ≫ SpectrumHo.hom f = 𝟙 (SpectrumHo.obj Y))
include hs

/-- coherent な切断は全整数次数で群の切断を誘導する。 -/
lemma section_map (j : ℤ) (a : homotopyGroup Y j) :
    homotopyMap f j (homotopyMap s j a) = a := by
  have hc : SpectrumHo.hom (s ≫ f) = SpectrumHo.hom (𝟙 Y) := by
    rw [SpectrumHo.hom_comp, hs, SpectrumHo.hom_id]
  have hp := SpectrumHo.homotopyMap_eq_of_hom_eq _ _ hc j
  have ha := DFunLike.congr_fun ((homotopyMap_comp s f j).symm.trans hp) a
  simpa only [homotopyMap_id, MonoidHom.id_apply, MonoidHom.comp_apply] using ha

lemma boundary_eq_one (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    homotopyFiberBoundary f j a = 1 :=
  (homotopy_exact_total_base f j a).2 ⟨homotopyMap s (j + 1) a, section_map f s hs _ a⟩

lemma inclusion_injective (j : ℤ) :
    Function.Injective (homotopyMap (homotopyFiberInclusion f) j) := by
  apply (injective_iff_map_eq_one _).2
  intro a ha
  obtain ⟨b, hb⟩ := (homotopy_exact_connecting_fiber f j a).1 ha
  rw [← hb, boundary_eq_one f s hs]

/-- 元の包含と coherent な切断による群の比較は全単射。 -/
lemma groupMap_bijective (j : ℤ) : Function.Bijective (SplitFiber.groupMap f s j) := by
  constructor
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hbd : b = d := by
      have he := congrArg (homotopyMap f j) h
      change homotopyMap f j (_ * _) = homotopyMap f j (_ * _) at he
      simpa only [map_mul, homotopyFiberInclusion_projection, section_map f s hs, one_mul]
        using he
    subst d
    have hac : a = c := inclusion_injective f s hs j (mul_right_cancel h)
    cases hac
    rfl
  · intro x
    let b := homotopyMap f j x
    have hk : homotopyMap f j (x * (homotopyMap s j b)⁻¹) = 1 := by
      rw [map_mul, map_inv, section_map f s hs]
      exact mul_inv_cancel _
    obtain ⟨a, ha⟩ := (homotopy_exact_fiber_total f j _).1 hk
    refine ⟨(a, b), ?_⟩
    change homotopyMap (homotopyFiberInclusion f) j a * homotopyMap s j b = x
    rw [ha]
    simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- coherent な切断を持つ元の BF fiber 群の積分解。 -/
def groupEquiv (j : ℤ) :
    homotopyGroup (homotopyFiber f) j × homotopyGroup Y j ≃* homotopyGroup X j :=
  MulEquiv.ofBijective (SplitFiber.groupMap f s j) (groupMap_bijective f s hs j)

end SerrePositivity.KST.LocalizingInvariants.CoherentSplitFiber
