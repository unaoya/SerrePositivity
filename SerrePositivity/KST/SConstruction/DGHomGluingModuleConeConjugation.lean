module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeElement
public import SerrePositivity.KST.SConstruction.DGHomGluingConeRightRestriction
public import SerrePositivity.KST.SConstruction.DGEndIsoConjugation

/-! # 元の右 cone 閉同型による三成分 End 作用の共役
概要：元の右包含を逆射とする閉同型で、三成分作用を元の右 End 元に戻す。
方針：元の Hom 評価と右包含への制限を使い、同じ逆律を適用する。
規約：左成分・第三成分に追加条件を置かない。使われ方：元の右対象 End の厳密回収。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 元の加群閉同型による End 共役の評価は、同じ閉射二つによる前後合成。 -/
lemma dgEndIsoHom_module_π {M N : ModuleCategory R E} (e : M ≅ N) (n : ℤ)
    (z : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M)).X n) (x : E) :
    (moduleHomπ R E (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N) x).f n ((dgEndIsoHom R (D := RightModule R E) e).f n z) =
      ((Cochain.ofHom ((moduleEvaluation R E x).map e.inv)).comp
        ((moduleHomπ R E (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) M) x).f n z) (zero_add n)).comp
        (Cochain.ofHom ((moduleEvaluation R E x).map e.hom)) (add_zero n) := by
  change (moduleHomπ R E (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) N) x).f n
    ((eHomWhiskerLeft (Complex R) N e.hom).f n
      ((eHomWhiskerRight (Complex R) e.inv M).f n z)) = _
  erw [moduleHomWhiskerLeft_apply_π R E (T := N) e.hom n
    ((eHomWhiskerRight (Complex R) e.inv M).f n z) x,
    moduleHomWhiskerRight_apply_π R E (P := M) e.inv n z x]
  rfl

/-- 逆射が元の標準右包含なら、共役した実 cone End 元は元の右成分に一致する。 -/
lemma dgGluingModuleConeElement_conjugate {M N : ModuleCategory R E}
    (f : M ⟶ N) (e : moduleCone R E f ≅ N) (he : e.inv = moduleConeInr R E f)
    {n m : ℤ} (a) (b) (h) (hm : m + 1 = n) :
    (dgEndIsoHom R (D := RightModule R E) e).f n
      (dgGluingModuleConeElement R E f f a b h hm) = b := by
  apply moduleHomElement_ext R E
    (M := ForgetEnrichment.to (Complex R) N)
    (N := ForgetEnrichment.to (Complex R) N)
  intro x
  erw [dgEndIsoHom_module_π R E (M := moduleCone R E f) (N := N),
    dgGluingModuleConeElement_π, he, moduleConeInr_eval,
    dgGluingConeCochain_inr, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp]
  have hi : mappingCone.inr ((moduleEvaluation R E x).map f) ≫
      (moduleEvaluation R E x).map e.hom = 𝟙 ((moduleEvaluation R E x).obj N) := by
    erw [← moduleConeInr_eval, ← he, ← CategoryTheory.Functor.map_comp,
      e.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [hi, Cochain.comp_id]

end SerrePositivity.KST.SConstruction
