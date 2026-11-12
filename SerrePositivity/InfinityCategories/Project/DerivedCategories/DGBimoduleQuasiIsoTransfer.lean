module
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Module.Disk
/-!
概要：右加群と全 Hom 自然な双加群の実同値を通じ、全次数全射性と準同型性を移す。
方針：同じ評価自然同型と同値の余単位に沿って、実射の性質を照合する。
規約：局所 Hom の平坦性は不要。使われ方：任意の双加群準同型の共通 span。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w)
  [DGCategory R B] [DGCategory R C] [Small.{u} B] [Small.{u} C]
/-- 実評価自然同型は、右加群射の全次数全射性を双加群射へ移す。 -/
lemma dgRightModuleBimodule_degree_surjective
    {M N : ModuleCategory R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ} (f : M ⟶ N)
    (hf : moduleDegreewiseSurjective R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ f)
    (b : B) (c : C) (n : ℤ) :
    Function.Surjective (((BimoduleCategory.valueEvaluation R B C b c).map
      ((rightModuleBimoduleEquivalence R B C).functor.map f)).f n) := by
  let e := rightModuleBimoduleEvaluationIso R B C b c
  have he : ((rightModuleBimoduleEquivalence R B C).functor ⋙
      BimoduleCategory.valueEvaluation R B C b c).map f =
    (e.app M).hom ≫
      (moduleEvaluation R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ (Opposite.op (Opposite.op b, c))).map f ≫
      (e.app N).inv := by
    have h := congrArg (fun k => k ≫ (e.app N).inv) (e.hom.naturality f)
    change _ ≫ (e.app N).hom ≫ (e.app N).inv =
      (e.app M).hom ≫ _ ≫ (e.app N).inv at h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using! h
  apply (ModuleCat.epi_iff_surjective _).1
  have := (moduleSurjectiveAt_iff_epi R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
    (Opposite.op (Opposite.op b, c)) n f).1 (hf _ n)
  change Epi ((((rightModuleBimoduleEquivalence R B C).functor ⋙
    BimoduleCategory.valueEvaluation R B C b c).map f).f n)
  rw [he, HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  infer_instance
omit [Small.{u} C] in
/-- 双加群射の全評価の全次数全射性は、同型による後合成で保たれる。 -/
lemma dgBimodule_degree_surjective_postIso {P Q Q' : BimoduleCategory R B C}
    (f : P ⟶ Q) (e : Q ≅ Q')
    (hf : ∀ b c n, Function.Surjective (((BimoduleCategory.valueEvaluation R B C b c).map f).f n))
    (b : B) (c : C) (n : ℤ) :
    Function.Surjective (((BimoduleCategory.valueEvaluation R B C b c).map (f ≫ e.hom)).f n) := by
  apply (ModuleCat.epi_iff_surjective _).1
  have := (ModuleCat.epi_iff_surjective _).2 (hf b c n)
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
  infer_instance
/-- 同じ実同値の逆は、双加群準同型を右加群準同型へ移す。 -/
lemma dgBimoduleInverse_quasiIso {P Q : BimoduleCategory R B C} (f : P ⟶ Q)
    (hf : BimoduleCategory.quasiIso R B C f) :
    moduleQuasiIso R (DGTensorCategory R Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence R B C).inverse.map f) := by
  let E := rightModuleBimoduleEquivalence R B C
  let W := BimoduleCategory.quasiIso R B C
  apply (rightModuleBimoduleEquivalence_quasiIso_iff R B C _).1
  have h : W ((E.counitIso.app P).hom ≫ f) := (W.cancel_left_of_respectsIso _ _).2 hf
  have hn := E.counitIso.hom.naturality f
  change E.functor.map (E.inverse.map f) ≫ (E.counitIso.app Q).hom =
    (E.counitIso.app P).hom ≫ f at hn
  rw [← hn] at h
  exact (W.cancel_right_of_respectsIso _ _).1 h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
