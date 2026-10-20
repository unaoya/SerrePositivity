module

public import SerrePositivity.KST.LocalizingInvariants.SplitProductAxes

/-!
概要：fiber 積比較の射影を補正する自己同値を構成する。
方針：第一射影を固定し、第二射影を比較と元の射の合成へ置換する。
規約：演算の標的変数の自然性を仮定しない。使われ方：元の両軸を保つ分裂。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SplitProduct

local instance shearSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (s : Y ⟶ X)

def shear : Binary.obj (homotopyFiber f) Y ⟶ Binary.obj (homotopyFiber f) Y :=
  Binary.lift (Binary.fst (homotopyFiber f) Y) (comparison f s ≫ f)

@[reassoc (attr := simp)]
lemma shear_fst : shear f s ≫ Binary.fst (homotopyFiber f) Y =
    Binary.fst (homotopyFiber f) Y := Binary.lift_fst _ _

@[reassoc (attr := simp)]
lemma shear_snd : shear f s ≫ Binary.snd (homotopyFiber f) Y = comparison f s ≫ f :=
  Binary.lift_snd _ _

variable (hs : SpectrumHo.hom s ≫ SpectrumHo.hom f = 𝟙 (SpectrumHo.obj Y))
include hs

lemma shear_map (j : ℤ) : homotopyMap (shear f s) j = MonoidHom.id _ := by
  ext a
  apply Binary.groupProjection_injective (homotopyFiber f) Y j
  apply Prod.ext
  · change homotopyMap (Binary.fst _ _) j (homotopyMap (shear f s) j a) = _
    rw [Binary.map_comp_apply, shear_fst]
    rfl
  · change homotopyMap (Binary.snd _ _) j (homotopyMap (shear f s) j a) = _
    rw [Binary.map_comp_apply, shear_snd, homotopyMap_comp, MonoidHom.comp_apply,
      comparison_map]
    change homotopyMap f j (homotopyMap (homotopyFiberInclusion f) j _ *
      homotopyMap s j _) = _
    rw [map_mul, homotopyFiberInclusion_projection, CoherentSplitFiber.section_map f s hs,
      one_mul]
    rfl

lemma shear_piIsomorphism : PiIsomorphism (shear f s) := by
  intro j
  rw [shear_map f s hs]
  exact Function.bijective_id

omit hs in
lemma shear_left : SpectrumHo.hom (Binary.inl (homotopyFiber f) Y) ≫
    SpectrumHo.hom (shear f s) = SpectrumHo.hom (Binary.inl (homotopyFiber f) Y) := by
  rw [← SpectrumHo.hom_comp]
  apply Binary.hom_ext
  · simp only [← SpectrumHo.hom_comp, Category.assoc, shear_fst]
  · simp only [← SpectrumHo.hom_comp, Category.assoc, shear_snd]
    rw [SpectrumHo.hom_comp (Binary.inl _ _) (comparison f s ≫ f),
      SpectrumHo.hom_comp (comparison f s) f, ← Category.assoc,
      comparison_left, SpectrumHo.fiber_inclusion_comp,
      Binary.inl_snd, SpectrumHo.hom_zero]

lemma shear_right : SpectrumHo.hom (Binary.inr (homotopyFiber f) Y) ≫
    SpectrumHo.hom (shear f s) = SpectrumHo.hom (Binary.inr (homotopyFiber f) Y) := by
  rw [← SpectrumHo.hom_comp]
  apply Binary.hom_ext
  · simp only [← SpectrumHo.hom_comp, Category.assoc, shear_fst]
  · simp only [← SpectrumHo.hom_comp, Category.assoc, shear_snd]
    rw [SpectrumHo.hom_comp (Binary.inr _ _) (comparison f s ≫ f),
      SpectrumHo.hom_comp (comparison f s) f, ← Category.assoc,
      comparison_right, hs, Binary.inr_snd, SpectrumHo.hom_id]

end SerrePositivity.KST.LocalizingInvariants.SplitProduct
