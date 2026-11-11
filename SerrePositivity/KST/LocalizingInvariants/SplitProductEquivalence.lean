module

public import SerrePositivity.KST.LocalizingInvariants.SplitProductShear

/-!
概要：coherent な切断を持つ BF fiber 列の Sp 積分解と元の三射への整合性。
方針：射影を補正する自己同値の逆を前合成し、両軸を固定する性質を使う。
規約：Sp の安定性も演算の標的自然性も要求しない。使われ方：局所化不変量の分裂。
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

local instance splitEquivalenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
  (hs : SpectrumHo.hom s ≫ SpectrumHo.hom f = 𝟙 (SpectrumHo.obj Y))

def shearIso : SpectrumHo.obj (Binary.obj (homotopyFiber f) Y) ≅
    SpectrumHo.obj (Binary.obj (homotopyFiber f) Y) := by
  haveI : IsIso (SpectrumHo.hom (shear f s)) :=
    isInvertible_of_piIsomorphism (shear f s) (shear_piIsomorphism f s hs)
  exact asIso (SpectrumHo.hom (shear f s))

/-- 実 BF 二項積と元の全空間の、元の Sp 内の同値。 -/
def equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj (homotopyFiber f) Y))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) := (shearIso f s hs).symm ≪≫ productVertexIso f s hs

lemma inverse_shear_left : SpectrumHo.hom (Binary.inl (homotopyFiber f) Y) ≫
    (shearIso f s hs).inv = SpectrumHo.hom (Binary.inl (homotopyFiber f) Y) := by
  have h := congrArg (fun m => m ≫ (shearIso f s hs).inv) (shear_left f s).symm
  change SpectrumHo.hom (Binary.inl _ _) ≫ (shearIso f s hs).inv =
    (SpectrumHo.hom (Binary.inl _ _) ≫ (shearIso f s hs).hom) ≫
      (shearIso f s hs).inv at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

lemma inverse_shear_right : SpectrumHo.hom (Binary.inr (homotopyFiber f) Y) ≫
    (shearIso f s hs).inv = SpectrumHo.hom (Binary.inr (homotopyFiber f) Y) := by
  have h := congrArg (fun m => m ≫ (shearIso f s hs).inv) (shear_right f s hs).symm
  change SpectrumHo.hom (Binary.inr _ _) ≫ (shearIso f s hs).inv =
    (SpectrumHo.hom (Binary.inr _ _) ≫ (shearIso f s hs).hom) ≫
      (shearIso f s hs).inv at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

lemma equivalence_inclusion : SpectrumHo.hom (Binary.inl (homotopyFiber f) Y) ≫
    (equivalence f s hs).hom = SpectrumHo.hom (homotopyFiberInclusion f) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫
    ((shearIso f s hs).inv ≫ SpectrumHo.hom (comparison f s)) = _
  rw [← Category.assoc, inverse_shear_left, comparison_left]

lemma equivalence_section : SpectrumHo.hom (Binary.inr (homotopyFiber f) Y) ≫
    (equivalence f s hs).hom = SpectrumHo.hom s := by
  change SpectrumHo.hom (Binary.inr _ _) ≫
    ((shearIso f s hs).inv ≫ SpectrumHo.hom (comparison f s)) = _
  rw [← Category.assoc, inverse_shear_right, comparison_right]

lemma equivalence_projection : (equivalence f s hs).hom ≫ SpectrumHo.hom f =
    SpectrumHo.hom (Binary.snd (homotopyFiber f) Y) := by
  change ((shearIso f s hs).inv ≫ SpectrumHo.hom (comparison f s)) ≫ SpectrumHo.hom f = _
  rw [Category.assoc, ← SpectrumHo.hom_comp, ← shear_snd, SpectrumHo.hom_comp]
  change (shearIso f s hs).inv ≫
    ((shearIso f s hs).hom ≫ SpectrumHo.hom (Binary.snd _ _)) = _
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.KST.LocalizingInvariants.SplitProduct
