module

public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

/-!
概要：一点 dg 加群の元の符号付き shift 包含が、元の閉零射に自然であることを示す。
方針：各次数で元の shift 同型を評価し、同じ符号の両側の合成を照合する。
規約：shift 包含と元の符号の定義は変更しない。
使われ方：3b-3 R6、元の native bar 列の全 HA 成分の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A]

/-- 元の符号付き shift 包含の全内部次数での同じ自然性。 -/
lemma pointShiftInElement_naturality (s : ℤ) {M N : ModuleCategory A PUnit.{1}}
    (f : M ⟶ N) (q r : ℤ) (hqr : q + -s = r) :
    ((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f q ≫
        (((moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) N)
          (shiftModule s (ForgetEnrichment.to (Complex A) N)) PUnit.unit).f (-s)
            (moduleShiftInElement A PUnit.{1} s (ForgetEnrichment.to (Complex A) N))).v q r hqr) =
      (((moduleHomπ A PUnit.{1} (ForgetEnrichment.to (Complex A) M)
          (shiftModule s (ForgetEnrichment.to (Complex A) M)) PUnit.unit).f (-s)
            (moduleShiftInElement A PUnit.{1} s (ForgetEnrichment.to (Complex A) M))).v q r hqr) ≫
        ((moduleEvaluation A PUnit.{1} PUnit.unit).map
          ((moduleShiftFunctor A PUnit.{1} s).map f)).f r := by
  have hq : q = r + s := by omega
  subst q
  rw [moduleShiftInElement_π, moduleShiftInElement_π, moduleShiftFunctor_map_eval]
  simp only [Cochain.units_smul_v,
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) (r + s) r hqr (r + s) (add_zero (r + s)),
    Cochain.ofHom_v, HomologicalComplex.id_f, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.id_comp, Category.comp_id,
    shiftFunctor_map_f', Linear.comp_units_smul, Linear.units_smul_comp]
  exact congrArg (fun z => (s * s + s * (s - 1) / 2).negOnePow • z)
    (Category.comp_id (((moduleEvaluation A PUnit.{1} PUnit.unit).map f).f (r + s)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
