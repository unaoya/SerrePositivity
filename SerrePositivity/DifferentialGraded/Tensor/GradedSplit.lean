module
public import SerrePositivity.DifferentialGraded.Tensor.GradedSplitLaws
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionLaws
public import SerrePositivity.DifferentialGraded.Tensor.KFlat
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # graded-split拡張のbalanced tensorによる保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 全作用と可換するgraded-split拡張をtensorした短い複体。 -/
def tensorShortComplex (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    ShortComplex (Complex A) :=
  ShortComplex.mk (rightTensorMap A D L f) (rightTensorMap A D L g) (by
    change (rightTensorFunctor A D L).map f ≫ (rightTensorFunctor A D L).map g = 0
    rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection, CategoryTheory.Functor.map_zero])

/-- tensor後のsection/retractionは各次数で短い複体を分裂する。 -/
def tensorDegreeSplitting (s : ModuleGradedSplit A D f g) (L : LeftModule A D) (n : ℤ) :
    ((tensorShortComplex A D s L).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting where
  r := (tensorRetractionCochain A D s L).v n n (add_zero n)
  s := (tensorSectionCochain A D s L).v n n (add_zero n)
  f_r := by
    have h := Cochain.congr_v (tensor_inclusion_retraction A D s L) n n (add_zero n)
    simpa only [tensorShortComplex, ShortComplex.map, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.id_f] using h
  s_g := by
    have h := Cochain.congr_v (tensor_section_projection A D s L) n n (add_zero n)
    simpa only [tensorShortComplex, ShortComplex.map, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj,
      Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f] using h
  id := by
    have h := Cochain.congr_v (tensor_decomposition A D s L) n n (add_zero n)
    simpa only [tensorShortComplex, ShortComplex.map, HomologicalComplex.eval_map,
      HomologicalComplex.eval_obj,
      Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      HomologicalComplex.id_f] using h

/-- graded-split拡張は任意の左加群とのtensorで短完全列になる。 -/
lemma tensorShortComplex_shortExact (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorShortComplex A D s L).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (tensorDegreeSplitting A D s L n).shortExact

/-- tensor後のacyclic性はgraded-split拡張の両端から中央へ伝わる。 -/
lemma tensor_acyclic_of_gradedSplit (s : ModuleGradedSplit A D f g) (L : LeftModule A D)
    (hM : (obj A D (ForgetEnrichment.to (Complex A) M) L).Acyclic)
    (hP : (obj A D (ForgetEnrichment.to (Complex A) P) L).Acyclic) :
    (obj A D (ForgetEnrichment.to (Complex A) N) L).Acyclic :=
  (tensorShortComplex_shortExact A D s L).acyclic_X₂ hM hP

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 相対K-flat性は全作用と可換するgraded-split拡張で閉じる。 -/
lemma moduleRelativeKFlat_of_gradedSplit (s : ModuleGradedSplit A D f g)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hP : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P)) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N) := by
  intro L hL
  exact BalancedTensor.tensor_acyclic_of_gradedSplit A D s L (hM L hL) (hP L hL)

end SerrePositivity.DifferentialGraded
