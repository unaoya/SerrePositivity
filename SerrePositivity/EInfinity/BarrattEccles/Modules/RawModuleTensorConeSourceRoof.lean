module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeSourceInverse

/-!
概要：元の全 cone と評価の合成を、同じ全 augmentation 逆による実屋根へ照合する。
方針：同じ逆の Arrow 等式を後合成し、元の定値端点への等式移送を保つ。
規約：HA §1.3.4、元の全パラメータと指定二脚。
使われ方：元の K の Hom 誘導射と同じ全 pinched 族の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma arrowPostcompEq {C : Type*} [Category* C] {x x' y z : C}
    (f : x ⟶ y) (g : x' ⟶ y) (h : Arrow.mk f = Arrow.mk g) (b : y ⟶ z) :
    Arrow.mk (f ≫ b) = Arrow.mk (g ≫ b) := by
  obtain ⟨hx, hy, hh⟩ := (Arrow.mk_eq_mk_iff f g).mp h
  simp only [eqToHom_refl, Category.comp_id] at hh
  apply (Arrow.mk_eq_mk_iff (f ≫ b) (g ≫ b)).mpr
  refine ⟨hx, rfl, ?_⟩
  simp only [eqToHom_refl, Category.comp_id]
  rw [hh, Category.assoc]

private lemma arrowTransportEq {C : Type*} [Category* C] {x y x' y' : C}
    (hx : x = x') (hy : y = y') (f : x ⟶ y) :
    Arrow.mk (eqToHom hx.symm ≫ f ≫ eqToHom hy) = Arrow.mk f := by
  cases hx
  cases hy
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

lemma strictRawModuleTensorConeSourceEvaluation_arrow :
    Arrow.mk (strictRawModuleTensorConeSourceFamilyHom A X P Q ≫
      strictRawModuleTensorElementSourceEvaluation A X P Q) =
    Arrow.mk (strictRawModuleTensorElementSourceRoof A X P Q) :=
  arrowPostcompEq _ _ (strictRawModuleTensorConeSourceFamilyHom_inverse_arrow A X P Q)
    (strictRawModuleTensorElementSourceEvaluation A X P Q)

lemma strictRawModuleTensorElementSourceRoofFamily_arrow :
    Arrow.mk (strictRawModuleTensorElementSourceRoofFamily A X P Q) =
      Arrow.mk (strictRawModuleTensorElementSourceRoof A X P Q) := by
  unfold strictRawModuleTensorElementSourceRoofFamily strictRawModuleDiagramSourceConstantIso
  exact arrowTransportEq
    (congrArg (fun f => SSet.HomotopyCategory.mk (functorVertex f))
      (strictRawModuleDiagramSource_const A X (I := strictRawModuleTensorElementIndex A X P Q)
        ((strictRawModuleProbeFunctor A X).obj P)))
    (congrArg (fun f => SSet.HomotopyCategory.mk (functorVertex f))
      (strictRawModuleDiagramSource_const A X (I := strictRawModuleTensorElementIndex A X P Q) Q))
    (strictRawModuleTensorElementSourceRoof A X P Q)

lemma strictRawModuleTensorConeSourceEvaluation_family_arrow :
    Arrow.mk (strictRawModuleTensorConeSourceFamilyHom A X P Q ≫
      strictRawModuleTensorElementSourceEvaluation A X P Q) =
    Arrow.mk (strictRawModuleTensorElementSourceRoofFamily A X P Q) :=
  (strictRawModuleTensorConeSourceEvaluation_arrow A X P Q).trans
    (strictRawModuleTensorElementSourceRoofFamily_arrow A X P Q).symm

end SerrePositivity.EInfinity.BarrattEccles
