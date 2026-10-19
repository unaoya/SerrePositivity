module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingPrecomposition
public import SerrePositivity.KST.Spectra.SpectrumMappingComponents
public import SerrePositivity.KST.Spectra.PathContractibility

/-!
概要：全 Hom の合成を対象の厳密等式で移送し、定値な第一因子を元の前合成へ同定する。
方針：対象の等式を消去し、直積の射影で定値パラメータを計算する。
規約：元の BF 射を保持。使われ方：比較三単体の右辺の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance mappingCompositionTransportSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の三つの対象の厳密等式による移送は、全 Hom の豊穣合成と両立する。 -/
lemma mappingComposition_transport {X Y Z X' Y' Z' : OmegaSpectrum.{u}}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') {A : SSet.{u}}
    (a : A ⟶ mappingSpace X Y) (b : A ⟶ mappingSpace Y Z) :
    lift (a ≫ eqToHom (congrArg₂ mappingSpace hX hY))
        (b ≫ eqToHom (congrArg₂ mappingSpace hY hZ)) ≫ mappingComposition X' Y' Z' =
      lift a b ≫ mappingComposition X Y Z ≫
        eqToHom (congrArg₂ mappingSpace hX hZ) := by
  cases hX
  cases hY
  cases hZ
  simp only [eqToHom_refl, Category.comp_id]

/-- 元の BF 射の定値な頂点との合成は、同じ BF 射の全 Hom 前合成。 -/
lemma mappingComposition_const_pre {X Y Z : OmegaSpectrum.{u}} (f : X ⟶ Y)
    {A : SSet.{u}} (b : A ⟶ mappingSpace Y Z) :
    lift (SSet.const (vertexOfHom f)) b ≫ mappingComposition X Y Z =
      b ≫ SpectrumMappingAcyclic.pre f Z := by
  change _ = b ≫ (λ_ (mappingSpace Y Z)).inv ≫
    eHomEquiv SSet f ▷ mappingSpace Y Z ≫ mappingComposition X Y Z
  have hf : eHomEquiv SSet f = vertexOfHomMap f := by
    change (SSet.unitHomEquiv _).symm ((SSet.unitHomEquiv _) (vertexOfHomMap f)) = _
    exact Equiv.symm_apply_apply _ _
  have hv : toUnit A ≫ vertexOfHomMap f = SSet.const (vertexOfHom f) := by
    have he := (SSet.unitHomEquiv _).symm_apply_apply (vertexOfHomMap f)
    change SSet.const (vertexOfHom f) = vertexOfHomMap f at he
    rw [← he, SSet.comp_const]
  have h : b ≫ (λ_ (mappingSpace Y Z)).inv ≫ eHomEquiv SSet f ▷ mappingSpace Y Z =
      lift (SSet.const (vertexOfHom f)) b := by
    rw [hf]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerRight_fst, leftUnitor_inv_fst_assoc,
        lift_fst]
      rw [← Category.assoc, comp_toUnit]
      exact hv
    · simp only [Category.assoc, whiskerRight_snd, leftUnitor_inv_snd,
        Category.comp_id]
      erw [lift_snd]
  calc
    _ = (b ≫ (λ_ (mappingSpace Y Z)).inv ≫ eHomEquiv SSet f ▷ mappingSpace Y Z) ≫
        mappingComposition X Y Z := congrArg (fun t ↦ t ≫ mappingComposition X Y Z) h.symm
    _ = _ := by simp only [Category.assoc]

end SerrePositivity.KST.Spectra.OmegaSpectrum
