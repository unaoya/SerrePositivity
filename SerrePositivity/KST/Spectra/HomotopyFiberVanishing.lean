module

public import SerrePositivity.KST.Spectra.SpectrumHomotopyFiber
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-!
概要：二つの隣接次数の単射・全射から、実際の homotopy fiber のホモトピー群を消す。
方針：長完全列の三つの位置を使い、fiber の任意の類が境界の零像となることを示す。
規約：実構成した BF homotopy fiber の群について述べる。可縮性は仮定しない。
使われ方：Goerss–Jardine VIII §§1–2、BF 1978 §2。収束と cohomology 消滅の適用。
-/

@[expose] public section
universe u
open CategoryTheory
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
noncomputable section

/-- 隣接次数での単射・全射から実際の homotopy fiber の群の消滅を得る。 -/
theorem homotopyFiberGroup_subsingleton_of_injective_surjective
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ)
    (hinj : Function.Injective (homotopyMap f j))
    (hsurj : Function.Surjective (homotopyMap f (j + 1))) :
    Subsingleton (homotopyGroup (homotopyFiber f) j) := by
  have hzero (a : homotopyGroup (homotopyFiber f) j) : a = 1 := by
    have ha : homotopyMap (homotopyFiberInclusion f) j a = 1 := by
      apply hinj
      rw [map_one]
      exact homotopyFiberInclusion_projection f j a
    obtain ⟨b, hb⟩ := (homotopy_exact_connecting_fiber f j a).mp ha
    obtain ⟨c, hc⟩ := hsurj b
    rw [← hb, ← hc, homotopyFiberBoundary_projection]
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

/-- 全整数次数の π 同型の実際の homotopy fiber は全整数次数の群が零。 -/
theorem PiIsomorphism.homotopyFiberGroup_subsingleton
    {X Y : OmegaSpectrum.{u}} {f : X ⟶ Y} (hf : PiIsomorphism f) (j : ℤ) :
    Subsingleton (homotopyGroup (homotopyFiber f) j) :=
  homotopyFiberGroup_subsingleton_of_injective_surjective f j (hf j).injective
    (hf (j + 1)).surjective

end
end SerrePositivity.KST.Spectra.OmegaSpectrum
