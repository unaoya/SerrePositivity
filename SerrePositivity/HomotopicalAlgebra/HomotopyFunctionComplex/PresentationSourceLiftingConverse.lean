module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLifting

/-! # Converse source lifting through an actual simplex presentation -/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.HomPresentation
variable {C : Type u} [Category.{v} C] {I : Type w} [Category.{t} I]
  (D : I ⥤ SimplexCategory) (s : Cocone (D ⋙ SSet.stdSimplex.{v}))
  (hs : IsColimit s) {A B : SimplexCategory ⥤ C}
  [HasColimit (D ⋙ A)] [HasColimit (D ⋙ B)] (α : A ⟶ B)
  [HasPushouts C] (c : Cocone D) [HasTerminal C] (targetObject : C)
  [HasLiftingProperty (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app targetObject)]

include s hs in
lemma relativeTensor_hasLiftingProperty :
    HasLiftingProperty (relativeTensorMap D α c) (terminal.from targetObject) := by
  constructor
  intro a b sq
  let u := pushout.inl (tensorSourceMap D α) (tensorMap D A c) ≫ a
  let v := pushout.inr (tensorSourceMap D α) (tensorMap D A c) ≫ a
  let u' := (homEquiv D s hs B).symm u
  let v' : SSet.stdSimplex.obj c.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj targetObject :=
    SSet.yonedaEquiv.symm v
  have sq' : CommSq u' (presentationMap D s hs c)
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app targetObject) v' := by
    constructor
    apply (homEquiv D s hs A).injective
    rw [← homEquiv_source_naturality, homEquiv_presentationMap]
    simp only [u', Equiv.apply_symm_apply]
    change tensorSourceMap D α ≫ (pushout.inl _ _ ≫ a) = tensorMap D A c ≫ (pushout.inr _ _ ≫ a)
    rw [← Category.assoc, pushout.condition, Category.assoc]
  refine CommSq.HasLift.mk' {
    l := SSet.yonedaEquiv sq'.lift
    fac_left := ?_
    fac_right := terminal.hom_ext _ _ }
  apply pushout.hom_ext
  · rw [inl_relativeTensorMap_assoc]
    have h := congrArg (homEquiv D s hs B) sq'.fac_left
    have he := homEquiv_presentationMap D s hs B c (SSet.yonedaEquiv sq'.lift)
    rw [Equiv.symm_apply_apply] at he
    simpa only [u', Equiv.apply_symm_apply] using he.symm.trans h
  · rw [inr_relativeTensorMap_assoc]
    have h := congrArg (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj targetObject))
      sq'.fac_right
    change α.app c.pt ≫ SSet.yonedaEquiv sq'.lift = SSet.yonedaEquiv v' at h
    simpa only [v', Equiv.apply_symm_apply] using h

end SerrePositivity.HomotopyFunctionComplex.HomPresentation
