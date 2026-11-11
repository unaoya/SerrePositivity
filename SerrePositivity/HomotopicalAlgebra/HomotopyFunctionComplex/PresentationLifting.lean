module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationHom
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! # Transport of lifting problems through a simplex presentation

The particular tensor map in C having LLP against p implies that the
presented simplicial map has LLP against `Hom(A,p)`. No global tensor
adjunction or infinite cocompleteness is assumed.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.HomPresentation
variable {C : Type u} [Category.{v} C] {I : Type w} [Category.{t} I]
  (D : I ⥤ SimplexCategory) (s : Cocone (D ⋙ SSet.stdSimplex.{v}))
  (hs : IsColimit s) (A : SimplexCategory ⥤ C) [HasColimit (D ⋙ A)]
  (c : Cocone D) {Y Z : C} (p : Y ⟶ Z)

lemma sourceSquare
    {a : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y}
    {b : SSet.stdSimplex.obj c.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z}
    (sq : CommSq a (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) b) :
    CommSq (homEquiv D s hs A a) (tensorMap D A c) p (SSet.yonedaEquiv b) := by
  constructor
  have h := congrArg (homEquiv D s hs A) sq.w
  rw [homEquiv_naturality] at h
  have hb := homEquiv_presentationMap D s hs A c (SSet.yonedaEquiv b)
  rw [Equiv.symm_apply_apply] at hb
  exact h.trans hb

variable [HasLiftingProperty (tensorMap D A c) p]

def liftStruct
    {a : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y}
    {b : SSet.stdSimplex.obj c.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z}
    (sq : CommSq a (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) b) :
    sq.LiftStruct where
  l := SSet.yonedaEquiv.symm (sourceSquare D s hs A c p sq).lift
  fac_left := by
    apply (homEquiv D s hs A).injective
    rw [homEquiv_presentationMap]
    exact (sourceSquare D s hs A c p sq).fac_left
  fac_right := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact (sourceSquare D s hs A c p sq).fac_right

lemma hasLiftingProperty :
    HasLiftingProperty (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) where
  sq_hasLift sq := CommSq.HasLift.mk' (liftStruct D s hs A c p sq)

end SerrePositivity.HomotopyFunctionComplex.HomPresentation
