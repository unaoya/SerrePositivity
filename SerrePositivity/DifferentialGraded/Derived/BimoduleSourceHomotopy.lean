module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSemifreeComparison

/-! # 実際のbimodule射の積dg圏表示でのホモトピーを主導来圏で同一視する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma bimoduleDerived_map_eq_of_inverse_source_homotopy
    {Q Q' : BimoduleCategory A C E} (f g : Q ⟶ Q')
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map f) =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map g)) :
    (bimoduleToDerived A C E).map f = (bimoduleToDerived A C E).map g := by
  let J := rightModuleBimoduleEquivalence A C E
  let T := bimoduleToDerived A C E
  have he := BimoduleSemifreeResolution.map_eq_of_source_homotopy
    (J.inverse.map f) (J.inverse.map g) h
  have hf := congrArg T.map (J.counitIso.hom.naturality f)
  have hg := congrArg T.map (J.counitIso.hom.naturality g)
  simp only [CategoryTheory.Functor.map_comp] at hf hg
  apply (Iso.cancel_iso_hom_left (T.mapIso (J.counitIso.app Q)) _ _).1
  exact hf.symm.trans ((congrArg (fun k => k ≫ T.map (J.counitIso.app Q').hom) he).trans hg)

end SerrePositivity.DifferentialGraded
