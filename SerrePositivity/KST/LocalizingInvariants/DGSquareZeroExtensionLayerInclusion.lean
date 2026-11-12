module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionHomology

/-!
概要：平方零拡大の実 kernel cocone から模型への包含と、層同型との整合を供給する。
方針：元の cocone 短完全列の包含を実複体同型で移し、元のホモロジー同型を計算する。
規約：実鎖写像を保持。使われ方：層の同型の自然性を元の射に対して証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  (a : W ⟶ SquareZero.algebra A N)

def layerInclusion : kernelComplex N ⟶ (model N a).X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a.hom (-(SquareZero.zeroSection A N).hom) ≫
    (DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)).inv

lemma layerInclusion_toCocone : layerInclusion N a ≫
    (DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a.hom (-(SquareZero.zeroSection A N).hom) := by
  simp only [layerInclusion, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma layerInclusion_homology_isIso (j : ℤ) (h₀ : IsZero (W.X.homology (j - 1)))
    (h₁ : IsZero (W.X.homology j)) : IsIso (homologyMap (layerInclusion N a) j) := by
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a.hom (-(SquareZero.zeroSection A N).hom)
  have : Mono (homologyMap i j) :=
    ((sequence_shortExact N a).homology_exact₁ (j - 1) j
      (by change j - 1 + 1 = j; omega)).mono_g (h₀.eq_of_src _ _)
  have : Epi (homologyMap i j) :=
    ((sequence_shortExact N a).homology_exact₂ j).epi_f (h₁.eq_of_tgt _ _)
  have : IsIso (homologyMap i j) := isIso_of_mono_of_epi _
  rw [layerInclusion, homologyMap_comp]
  infer_instance

lemma layerInclusion_layerHomologyIso (j : ℤ) (h₀ : IsZero (W.X.homology (j - 1)))
    (h₁ : IsZero (W.X.homology j)) : homologyMap (layerInclusion N a) j ≫
      (layerHomologyIso N a j h₀ h₁).hom = (kernelHomologyIso N j).hom := by
  let e := DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a.hom (-(SquareZero.zeroSection A N).hom)
  have : Mono (homologyMap i j) :=
    ((sequence_shortExact N a).homology_exact₁ (j - 1) j
      (by change j - 1 + 1 = j; omega)).mono_g (h₀.eq_of_src _ _)
  have : Epi (homologyMap i j) :=
    ((sequence_shortExact N a).homology_exact₂ j).epi_f (h₁.eq_of_tgt _ _)
  have : IsIso (homologyMap i j) := isIso_of_mono_of_epi _
  have he : homologyMap e.inv j ≫ homologyMap e.hom j = 𝟙 _ := by
    rw [← homologyMap_comp, e.inv_hom_id, homologyMap_id]
  change homologyMap (i ≫ e.inv) j ≫
    (homologyMap e.hom j ≫ (asIso (homologyMap i j)).inv ≫ (kernelHomologyIso N j).hom) = _
  rw [homologyMap_comp, Category.assoc, ← Category.assoc (homologyMap e.inv j), he]
  simp

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
