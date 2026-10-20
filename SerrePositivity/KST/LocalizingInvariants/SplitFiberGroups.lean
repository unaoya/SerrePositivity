module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyFiber

/-!
概要：切断を持つ実 BF 射の fiber 長完全列の分裂。
方針：切断で接続射を消し、fiber 包含と切断の積で群の同型を作る。
規約：群の積分解であり、Sp の積分解そのものは別工程。使われ方：K-5 の分裂比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants

namespace SplitFiber
variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)
include hs

/-- 厳密な切断は全整数次数で群の切断を誘導する。 -/
lemma section_map (j : ℤ) (a : homotopyGroup Y j) :
    homotopyMap f j (homotopyMap s j a) = a := by
  have h := DFunLike.congr_fun (homotopyMap_comp s f j) a
  simpa only [hs, homotopyMap_id, MonoidHom.id_apply, MonoidHom.comp_apply] using h.symm

/-- 切断があれば全整数次数の接続射は零。 -/
lemma boundary_eq_one (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    homotopyFiberBoundary f j a = 1 :=
  (homotopy_exact_total_base f j a).2 ⟨homotopyMap s (j + 1) a, section_map f s hs _ a⟩

/-- 分裂列では fiber の包含が各整数次数で単射。 -/
lemma inclusion_injective (j : ℤ) :
    Function.Injective (homotopyMap (homotopyFiberInclusion f) j) := by
  apply (injective_iff_map_eq_one _).2
  intro a ha
  obtain ⟨b, hb⟩ := (homotopy_exact_connecting_fiber f j a).1 ha
  rw [← hb, boundary_eq_one f s hs]

/-- fiber の類と底の類を、包含と切断を用いて全空間の類に送る。 -/
def groupMap (j : ℤ) :
    homotopyGroup (homotopyFiber f) j × homotopyGroup Y j →* homotopyGroup X j where
  toFun a := homotopyMap (homotopyFiberInclusion f) j a.1 * homotopyMap s j a.2
  map_one' := by
    change homotopyMap (homotopyFiberInclusion f) j 1 * homotopyMap s j 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl

/-- 長完全列の完全性から分裂比較の全単射性を得る。 -/
lemma groupMap_bijective (j : ℤ) : Function.Bijective (groupMap f s j) := by
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

/-- 全整数次数での実際の fiber 群と底の群の積分解。 -/
def groupEquiv (j : ℤ) :
    homotopyGroup (homotopyFiber f) j × homotopyGroup Y j ≃* homotopyGroup X j :=
  MulEquiv.ofBijective (groupMap f s j) (groupMap_bijective f s hs j)

end SplitFiber
end SerrePositivity.KST.LocalizingInvariants
