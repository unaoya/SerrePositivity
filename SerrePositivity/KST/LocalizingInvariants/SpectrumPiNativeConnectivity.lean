module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPiConnectivity
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyComparison

/-!
概要：元の BF 整数 π の単射・全射を、同じ h Sp の射の整数 π へ移す。
方針：元の BF 群との比較同型の自然性で、同じ元の射の作用を比較する。
規約：群や射を変更しない。使われ方：実 dg 代数の値の塔の連結度判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo
variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ)

lemma piFunctor_map_injective_of_native
    (h : Function.Injective (OmegaSpectrum.homotopyMap f j)) :
    Function.Injective ((piFunctor j).map (hom f)).hom := by
  intro x y hxy
  have hx := congrArg (fun m => m.hom x) (piComparison_naturality f j)
  have hy := congrArg (fun m => m.hom y) (piComparison_naturality f j)
  have he := hx.symm.trans
    ((congrArg (piComparison Y j).hom.hom hxy).trans hy)
  exact (ConcreteCategory.bijective_of_isIso (piComparison X j).hom).1 (h he)

lemma piFunctor_map_surjective_of_native
    (h : Function.Surjective (OmegaSpectrum.homotopyMap f j)) :
    Function.Surjective ((piFunctor j).map (hom f)).hom := by
  intro y
  obtain ⟨z, hz⟩ := h ((piComparison Y j).hom.hom y)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (piComparison X j).hom).2 z
  refine ⟨x, (ConcreteCategory.bijective_of_isIso (piComparison Y j).hom).1 ?_⟩
  have he := congrArg (fun m => m.hom x) (piComparison_naturality f j)
  exact he.trans ((congrArg (OmegaSpectrum.homotopyMap f j) hx).trans hz)

lemma isPiConnected_of_native (n : ℤ)
    (hi : ∀ j : ℤ, j < n → Function.Injective (OmegaSpectrum.homotopyMap f j))
    (hs : ∀ j : ℤ, j ≤ n → Function.Surjective (OmegaSpectrum.homotopyMap f j)) :
    IsPiConnected (hom f) n :=
  ⟨fun j hj => piFunctor_map_injective_of_native f j (hi j hj),
    fun j hj => piFunctor_map_surjective_of_native f j (hs j hj)⟩

end SerrePositivity.KST.LocalizingInvariants.SpectrumHo
