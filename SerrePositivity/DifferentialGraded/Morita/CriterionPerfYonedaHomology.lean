module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfYonedaAction

/-! # 全ての表現可能対象間の導来射に対する H⁰ 比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- dg Yoneda の閉次数零制限は、表現可能加群間の全ての閉零射を与える。 -/
lemma criterionPerfYonedaClosed_map_surjective (d d' : ClosedCategory A D) :
    Function.Surjective ((dgYoneda A D).onClosed.map (X := d) (Y := d')) := by
  intro g
  let c := complexMapZeroCycle A (dgYonedaIso A (D := D) d (representable A (D := D) d')).hom
    (closedHomEquiv A (RightModule A D) _ _ g)
  refine ⟨(closedHomEquiv A D d d').symm c, ?_⟩
  apply (closedHomEquiv A (RightModule A D) _ _).injective
  rw [← criterionPerf_closedHomEquiv_map, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (dgYonedaIso A (D := D) d (representable A (D := D) d')).inv.f 0
    ((dgYonedaIso A (D := D) d (representable A (D := D) d')).hom.f 0
      (closedHomEquiv A (RightModule A D) _ _ g).val) = _
  rw [← ModuleCat.comp_apply, ← comp_f, Iso.hom_inv_id, id_f, ModuleCat.id_apply]

/-- 表現可能対象間の導来射は、元の dg 圏の閉零射の Yoneda 像で表せる。 -/
lemma criterionPerfYonedaDerived_map_surjective (d d' : ClosedCategory A D) :
    Function.Surjective (fun f : d ⟶ d' =>
      (moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)) := by
  intro f
  obtain ⟨g, hg⟩ := (moduleProjectiveDerivedHomEquiv A D
    (representable_homotopicallyProjective A D d) _).surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  obtain ⟨g, rfl⟩ := criterionPerfYonedaClosed_map_surjective A D d d' g
  rw [moduleProjectiveDerivedHomEquiv_map] at hg
  exact ⟨g, hg⟩

/-- 実際の Yoneda 射を、元の全 Hom 複体の H⁰ 類に送る公式。 -/
lemma criterionPerfYonedaDerivedHomology_closed {d d' : ClosedCategory A D} (f : d ⟶ d') :
    moduleRepresentableDerivedHomologyEquiv A D d _
        ((moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)) =
      complexZeroHomologyClass A (homObject A D d d') (closedHomEquiv A D d d' f) := by
  rw [moduleRepresentableDerivedHomologyEquiv_map, complexZeroHomologyClass_naturality]
  congr 1
  erw [← criterionPerf_closedHomEquiv_map A (dgYoneda A D) f]
  apply Subtype.ext
  change (dgYonedaIso A (D := D) d (representable A (D := D) d')).hom.f 0
    ((dgYonedaIso A (D := D) d (representable A (D := D) d')).inv.f 0
      (closedHomEquiv A D d d' f).val) = _
  rw [← ModuleCat.comp_apply, ← comp_f, Iso.inv_hom_id, id_f, ModuleCat.id_apply]

variable (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 閉零代表を指定しない任意の導来射についての、実際の主作用と H⁰ 比較の可換式。 -/
lemma criterionPerfYonedaMainActionMap_homology_zero_all
    (d d' : ClosedCategory A D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d))
    (f : criterionPerfRepresentable A D d ⟶ criterionPerfRepresentable A D d') :
    criterionPerfColumnDerivedHomEquiv A D E P d d' R
        (criterionPerfYonedaMainActionMap A D E P d d' f) =
      homologyMap (criterionPerfHomComparison A D E P d d' R) 0
        (moduleRepresentableDerivedHomologyEquiv A D d _ f) := by
  obtain ⟨f, rfl⟩ := criterionPerfYonedaDerived_map_surjective A D d d' f
  dsimp only
  erw [criterionPerfYonedaDerivedHomology_closed A D f]
  exact criterionPerfYonedaMainActionMap_homology_zero A D E P f R

/-- 全 Hom 比較の次数零での擬同型性と、主作用の実際の射写像の全単射性との同値。
これは全次数の擬同型条件の次数零の部分である。 -/
lemma criterionPerfHomComparison_quasiIsoAt_zero_iff
    (d d' : ClosedCategory A D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIsoAt (criterionPerfHomComparison A D E P d d' R) 0 ↔
      Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := criterionPerfRepresentable A D d) (Y := criterionPerfRepresentable A D d')) := by
  let eS := moduleRepresentableDerivedHomologyEquiv A D d
    (ForgetEnrichment.of (Complex A) (representable A (D := D) d'))
  let eT := criterionPerfColumnDerivedHomEquiv A D E P d d' R
  let t := criterionPerfYonedaMainActionMap A D E P d d'
  let a := homologyMap (criterionPerfHomComparison A D E P d d' R) 0
  have heq : eT ∘ t = a ∘ eS := funext
    (criterionPerfYonedaMainActionMap_homology_zero_all A D E P d d' R)
  have ht : Function.Bijective t ↔ Function.Bijective a :=
    (Function.Bijective.of_comp_iff' eT.bijective t).symm.trans (by
      rw [heq]
      exact Function.Bijective.of_comp_iff a eS.bijective)
  have hm : Function.Bijective t ↔ Function.Bijective
      ((kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
        (X := criterionPerfRepresentable A D d) (Y := criterionPerfRepresentable A D d')) :=
    Function.Bijective.of_comp_iff'
      (Iso.homCongr ((criterionPerfYonedaMainDerivedIso A D E P).app d)
        ((criterionPerfYonedaMainDerivedIso A D E P).app d')).bijective _
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ht.symm.trans hm

end SerrePositivity.DifferentialGraded.Morita
