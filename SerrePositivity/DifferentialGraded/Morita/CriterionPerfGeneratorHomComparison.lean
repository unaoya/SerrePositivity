module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfRelativeFullyFaithful
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfFullHomCriterion
/-!
概要：指定生成集合の局所 Hom 複体条件を全 Perf の Hom 比較へ延長する。
方針：同じ kernel の全シフト比較から、両変数の cone 二対三・retract 帰納を適用する。
規約：通常代表の解消比較を保持し、生成条件を H⁰ 充満忠実性に置き換えない。
使われ方：D-17 の graph kernel による元の dg 関手の全 Hom 生成判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

lemma criterionPerfHomComparison_iff_shiftedRepresentableMaps (d d' : D) :
    QuasiIso (criterionPerfHomComparison A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))) ↔
    ∀ (m n : ℤ), Function.Bijective
      ((kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
        (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧)) := by
  let K := (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)
  let F := kernelDerivedTensor A D E K
  let := criterionPerfKernelCommShift A D E K
  constructor
  · intro h
    have hs (s : ℤ) : Function.Bijective
        (F.map (X := (criterionPerfRepresentable A D d)⟦s⟧)
          (Y := criterionPerfRepresentable A D d')) := by
      have hb := (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
        (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).1 h s
      exact homComparison_bijective_of_iso F
        (((moduleToDerived A D).commShiftIso s).app
          (ForgetEnrichment.of (Complex A) (representable A d))) (Iso.refl _) hb
    intro m n
    exact homComparison_bijective_of_iso F
      ((shiftFunctorAdd' (DerivedModuleCategory A D) (m - n) n m (by omega)).symm.app _)
      (Iso.refl _) (homComparison_bijective_shift_both F (hs (m - n)) n)
  · intro h
    apply (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).2
    intro s
    exact homComparison_bijective_of_iso F
      (((moduleToDerived A D).commShiftIso s).app
        (ForgetEnrichment.of (Complex A) (representable A d))).symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _) (h s 0)

lemma criterionPerfFullHomQuasiIso_of_generators (G : Set D)
    (hG : modulePerfectOver A D G = modulePerfect A D)
    (h : ∀ d ∈ G, ∀ d' ∈ G,
      QuasiIso (criterionPerfHomComparison A D E P d d'
        (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d)))) :
    criterionPerfFullHomQuasiIso A D E P := by
  let K := (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)
  let F := kernelDerivedTensor A D E K
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  apply (criterionPerfFullHomQuasiIso_iff_representableMaps A D E P).2
  intro d d' m n
  apply criterionPerf_hom_bijective_of_generators A D E F G
    (fun x hx y hy => (criterionPerfHomComparison_iff_shiftedRepresentableMaps
      A D E P x y).1 (h x hx y hy))
  · rw [hG]
    exact (modulePerfect A D).le_shift m _ (modulePerfectOver_representable A D d (Set.mem_univ _))
  · rw [hG]
    exact (modulePerfect A D).le_shift n _ (modulePerfectOver_representable A D d' (Set.mem_univ _))

end SerrePositivity.DifferentialGraded.Morita
