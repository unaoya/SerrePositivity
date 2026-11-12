module

public import SerrePositivity.KST.LocalizingInvariants.CochainSplitCoconeHomology
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexMappingCoconeBiprodExact
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：実平方零 class の経路拡大の射影と、元の係数による層ホモロジーを計算する。
方針：元の差の cocone の短完全列を使い、零切断の fiber を係数の負一 shift へ比較する。
規約：元の実射影を使用。使われ方：Postnikov 像拡大の連結度とホモロジー像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  (a : W ⟶ SquareZero.algebra A N)

abbrev model := DGAlgebra.HomotopyPullbackModel.algebra R a (SquareZero.zeroSection A N)
abbrev kernelComplex := mappingCocone (-(SquareZero.zeroSection A N).hom)
abbrev sequence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex a.hom (-(SquareZero.zeroSection A N).hom)

lemma sequence_shortExact : (sequence N a).ShortExact :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodShortComplex_shortExact _ _

def kernelHomologyIso (j : ℤ) : (kernelComplex N).homology j ≅ N.X.homology (j - 1) :=
  cochainNegInlCoconeHomologyIso A.X N.X j

lemma projection_quasiIsoAt (j : ℤ) (h₀ : IsZero (N.X.homology (j - 1)))
    (h₁ : IsZero (N.X.homology j)) :
    QuasiIsoAt (DGAlgebra.HomotopyPullbackModel.left R a (SquareZero.zeroSection A N)).hom j := by
  have hz : IsZero ((kernelComplex N).homology j) := h₀.of_iso (kernelHomologyIso N j)
  have hz' : IsZero ((kernelComplex N).homology (j + 1)) := by
    have h : IsZero (N.X.homology (j + 1 - 1)) := by simpa using h₁
    exact h.of_iso (kernelHomologyIso N (j + 1))
  let p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodProjection a.hom (-(SquareZero.zeroSection A N).hom)
  have : Mono (homologyMap p j) :=
    ((sequence_shortExact N a).homology_exact₂ j).mono_g (hz.eq_of_src _ _)
  have : Epi (homologyMap p j) :=
    ((sequence_shortExact N a).homology_exact₃ j (j + 1)
      (by change j + 1 = j + 1; rfl)).epi_f (hz'.eq_of_tgt _ _)
  have : QuasiIsoAt p j := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_of_mono_of_epi _
  let e := DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)
  have : QuasiIso e.hom := quasiIso_of_isIso _
  have hc : QuasiIsoAt (e.hom ≫ p) j := inferInstance
  have he : e.hom ≫ p =
      (DGAlgebra.HomotopyPullbackModel.left R a (SquareZero.zeroSection A N)).hom :=
    DGAlgebra.HomotopyPullbackModel.toMappingCocone_left R _ _
  exact (congrArg (fun t => QuasiIsoAt t j) he).mp hc

lemma model_homology_isZero (j : ℤ) (hN : IsZero (N.X.homology (j - 1)))
    (hW : IsZero (W.X.homology j)) : IsZero ((model N a).X.homology j) := by
  have hz : IsZero ((kernelComplex N).homology j) := hN.of_iso (kernelHomologyIso N j)
  have hm := ((sequence_shortExact N a).homology_exact₂ j).isZero_X₂
    (hz.eq_of_src _ _) (hW.eq_of_tgt _ _)
  exact hm.of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso
    (DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)))

def layerHomologyIso (j : ℤ) (h₀ : IsZero (W.X.homology (j - 1)))
    (h₁ : IsZero (W.X.homology j)) : (model N a).X.homology j ≅ N.X.homology (j - 1) := by
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a.hom (-(SquareZero.zeroSection A N).hom)
  have : Mono (homologyMap i j) :=
    ((sequence_shortExact N a).homology_exact₁ (j - 1) j
      (by change j - 1 + 1 = j; omega)).mono_g (h₀.eq_of_src _ _)
  have : Epi (homologyMap i j) :=
    ((sequence_shortExact N a).homology_exact₂ j).epi_f (h₁.eq_of_tgt _ _)
  have : IsIso (homologyMap i j) := isIso_of_mono_of_epi _
  exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) j).mapIso
    (DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)) ≪≫
      (asIso (homologyMap i j)).symm ≪≫ kernelHomologyIso N j

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
