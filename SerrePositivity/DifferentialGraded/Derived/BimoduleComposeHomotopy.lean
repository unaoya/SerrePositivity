module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleCylinder
public import SerrePositivity.DifferentialGraded.Module.Homotopy

/-! # 任意の前因子とのbimodule合成後にsourceホモトピーを同一視する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E] (P : BimoduleCategory A B C)

/-- すべての準同型の保存を要求せず、標準cylinderの射影だけを反転して境界を同一視する。 -/
lemma composeAfter_equalizes_source_boundary
    {M N : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ) f g) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map f)) =
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map g)) := by
  let H := (rightModuleBimoduleEquivalence A C E).functor ⋙
    composeAfter A B C E P ⋙ bimoduleToDerived A B E
  let I := modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M
  let d := moduleCylinderDesc A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ f g h
  have : IsIso (H.map I.π) := bimoduleToDerived_inverts A B E _
    (composeAfter_sourcePrecylinderProjection_quasiIso A B C E P M)
  have hi : H.map I.i₀ = H.map I.i₁ := by
    apply (Iso.cancel_iso_hom_right _ _ (asIso (H.map I.π))).1
    change H.map I.i₀ ≫ H.map I.π = H.map I.i₁ ≫ H.map I.π
    exact (H.map_comp _ _).symm.trans
      ((congrArg H.map I.i₀_π).trans
        ((congrArg H.map I.i₁_π.symm).trans (H.map_comp _ _)))
  change H.map f = H.map g
  calc
    _ = H.map (I.i₀ ≫ d) := congrArg H.map (moduleCylinderDesc_i₀ A _ f g h).symm
    _ = H.map I.i₀ ≫ H.map d := H.map_comp _ _
    _ = H.map I.i₁ ≫ H.map d := congrArg (fun k => k ≫ H.map d) hi
    _ = H.map (I.i₁ ≫ d) := (H.map_comp _ _).symm
    _ = _ := congrArg H.map (moduleCylinderDesc_i₁ A _ f g h)

lemma composeAfter_map_eq_of_source_homotopy
    {M N : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ} (f g : M ⟶ N)
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map f =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map g) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map f)) =
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map g)) :=
  composeAfter_equalizes_source_boundary A B C E P f g
    ((moduleHomotopy_nonempty_iff A _ f g).1 ((moduleToHomotopy_map_eq_iff A _ f g).1 h))

/-- 任意の実際のbimodule射も、積dg圏表示でホモトピックなら合成後の導来圏で一致する。 -/
lemma composeAfter_map_eq_of_inverse_source_homotopy
    {Q Q' : BimoduleCategory A C E} (f g : Q ⟶ Q')
    (h : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map f) =
      (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A C E).inverse.map g)) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map f) =
      (bimoduleToDerived A B E).map ((composeAfter A B C E P).map g) := by
  let J := rightModuleBimoduleEquivalence A C E
  let T := composeAfter A B C E P ⋙ bimoduleToDerived A B E
  have he := composeAfter_map_eq_of_source_homotopy A B C E P
    (J.inverse.map f) (J.inverse.map g) h
  have hf := congrArg T.map (J.counitIso.hom.naturality f)
  have hg := congrArg T.map (J.counitIso.hom.naturality g)
  simp only [CategoryTheory.Functor.map_comp] at hf hg
  change T.map f = T.map g
  apply (Iso.cancel_iso_hom_left (T.mapIso (J.counitIso.app Q)) _ _).1
  exact hf.symm.trans ((congrArg (fun k => k ≫ T.map (J.counitIso.app Q').hom) he).trans hg)

end SerrePositivity.DifferentialGraded.BimoduleTensor
