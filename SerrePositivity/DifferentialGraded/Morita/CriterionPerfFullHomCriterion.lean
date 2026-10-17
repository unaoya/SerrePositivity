module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTensorHomComparison
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfConditions

/-! # 全 Hom 複体の条件と、実際の主作用の全整数 shift 上の射比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory

private lemma map_bijective_natIso_iff
    {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]
    {F G : C ⥤ B} (e : F ≅ G) (X Y : C) :
    Function.Bijective (F.map (X := X) (Y := Y)) ↔
      Function.Bijective (G.map (X := X) (Y := Y)) := by
  have heq : (Iso.homCongr (e.app X) (e.app Y)) ∘ F.map = G.map := by
    funext f
    exact (congrArg (fun k => e.inv.app X ≫ k) (e.hom.naturality f)).trans
      (e.inv_hom_id_app_assoc X _)
  rw [← heq]
  exact (Function.Bijective.of_comp_iff' (Iso.homCongr (e.app X) (e.app Y)).bijective _).symm

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 全 Hom 条件を通常の射集合に置き換えず、その全次数の計算から全 shift の射比較を得る。 -/
lemma criterionPerfFullHomQuasiIso_iff_representableMaps :
    criterionPerfFullHomQuasiIso A D E P ↔
      ∀ (d d' : D) (m n : ℤ), Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (criterionPerfRepresentable A D d)⟦m⟧)
          (Y := (criterionPerfRepresentable A D d')⟦n⟧)) := by
  let K := (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)
  let F := kernelDerivedTensor A D E K
  let := criterionPerfKernelCommShift A D E K
  constructor
  · intro h
    have hs (d d' : D) (s : ℤ) : Function.Bijective
        (F.map (X := (criterionPerfRepresentable A D d)⟦s⟧)
          (Y := criterionPerfRepresentable A D d')) := by
      have hb := (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
        (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).1 (h d d') s
      exact homComparison_bijective_of_iso F
        (((moduleToDerived A D).commShiftIso s).app
          (ForgetEnrichment.of (Complex A) (representable A d))) (Iso.refl _) hb
    intro d d' m n
    exact homComparison_bijective_of_iso F
      ((shiftFunctorAdd' (DerivedModuleCategory A D) (m - n) n m (by omega)).symm.app _)
      (Iso.refl _) (homComparison_bijective_shift_both F (hs d d' (m - n)) n)
  · intro h d d'
    apply (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).2
    intro s
    exact homComparison_bijective_of_iso F
      (((moduleToDerived A D).commShiftIso s).app
        (ForgetEnrichment.of (Complex A) (representable A d))).symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _) (h d d' s 0)

/-- 代表の存在で定式化した主 kernel の全 Hom 条件と、実際の作用の全 shift の比較。 -/
lemma criterionPerfKernelFullHomQuasiIso_iff_representableMaps (K : Kernel A D E) :
    criterionPerfKernelFullHomQuasiIso A D E K ↔
      ∀ (d d' : D) (m n : ℤ), Function.Bijective
        ((kernelDerivedTensor A D E K).map
          (X := (criterionPerfRepresentable A D d)⟦m⟧)
          (Y := (criterionPerfRepresentable A D d')⟦n⟧)) := by
  constructor
  · rintro ⟨P, ⟨e⟩, h⟩ d d' m n
    exact (map_bijective_natIso_iff ((kernelDerivedTensorFunctor A D E).mapIso e) _ _).1
      ((criterionPerfFullHomQuasiIso_iff_representableMaps A D E
        (BimoduleCategory.underlying A E D P)).1 h d d' m n)
  · intro h
    obtain ⟨⟨P⟩⟩ := K
    refine ⟨P, ⟨Iso.refl _⟩, ?_⟩
    exact (criterionPerfFullHomQuasiIso_iff_representableMaps A D E
      (BimoduleCategory.underlying A E D P)).2 h

/-- 主 kernel の条件は、どの通常代表で全 Hom を計算しても同じ条件となる。 -/
lemma criterionPerfKernelFullHomQuasiIso_model_iff
    (Q : BimoduleCategory A E D) (K : Kernel A D E)
    (e : (bimoduleToDerived A E D).obj Q ≅ K) :
    criterionPerfKernelFullHomQuasiIso A D E K ↔
      criterionPerfFullHomQuasiIso A D E (BimoduleCategory.underlying A E D Q) := by
  constructor
  · intro h
    apply (criterionPerfFullHomQuasiIso_iff_representableMaps A D E _).2
    intro d d' m n
    exact (map_bijective_natIso_iff ((kernelDerivedTensorFunctor A D E).mapIso e) _ _).2
      ((criterionPerfKernelFullHomQuasiIso_iff_representableMaps A D E K).1 h d d' m n)
  · exact criterionPerfKernelFullHomQuasiIso_of_model A D E Q K e

end SerrePositivity.DifferentialGraded.Morita
