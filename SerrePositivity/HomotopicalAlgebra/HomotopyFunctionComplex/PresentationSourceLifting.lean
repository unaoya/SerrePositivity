module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationLifting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Source-variable lifting through an actual simplex presentation

The relative tensor is a pushout of the source transformation along its
boundary tensor. Lifting this map into a fibrant target fills the corresponding
simplicial boundary in the contravariant Hom variable.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.HomPresentation
variable {C : Type u} [Category.{v} C] {I : Type w} [Category.{t} I]
  (D : I ⥤ SimplexCategory) (s : Cocone (D ⋙ SSet.stdSimplex.{v}))
  (hs : IsColimit s) {A B : SimplexCategory ⥤ C}
  [HasColimit (D ⋙ A)] [HasColimit (D ⋙ B)] (α : A ⟶ B)

abbrev tensorSourceMap : colimit (D ⋙ A) ⟶ colimit (D ⋙ B) :=
  colimMap (Functor.whiskerLeft D α)

@[reassoc (attr := simp)]
lemma ι_tensorSourceMap (i : I) :
    colimit.ι (D ⋙ A) i ≫ tensorSourceMap D α =
      α.app (D.obj i) ≫ colimit.ι (D ⋙ B) i :=
  ι_colimMap _ _

lemma homEquiv_source_naturality {Y : C} (f : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Y) :
    tensorSourceMap D α ≫ homEquiv D s hs B f =
      homEquiv D s hs A (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) := by
  apply colimit.hom_ext
  intro i
  rw [ι_homEquiv]
  have h := congrArg (fun k ↦ k ≫ homEquiv D s hs B f) (ι_tensorSourceMap D α i)
  exact (Category.assoc _ _ _).symm.trans (h.trans ((Category.assoc _ _ _).trans
    (congrArg (fun k ↦ α.app (D.obj i) ≫ k) (ι_homEquiv D s hs B f i)))
    )

lemma tensorSourceMap_tensorMap (c : Cocone D) :
    tensorSourceMap D α ≫ tensorMap D B c = tensorMap D A c ≫ α.app c.pt := by
  apply colimit.hom_ext
  intro i
  simp only [ι_tensorSourceMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
  exact (α.naturality (c.ι.app i)).symm

variable [HasPushouts C] (c : Cocone D)

def relativeTensorMap :
    pushout (tensorSourceMap D α) (tensorMap D A c) ⟶ B.obj c.pt :=
  pushout.desc (tensorMap D B c) (α.app c.pt) (tensorSourceMap_tensorMap D α c)

@[reassoc (attr := simp)]
lemma inl_relativeTensorMap :
    pushout.inl (tensorSourceMap D α) (tensorMap D A c) ≫ relativeTensorMap D α c =
      tensorMap D B c := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_relativeTensorMap :
    pushout.inr (tensorSourceMap D α) (tensorMap D A c) ≫ relativeTensorMap D α c =
      α.app c.pt := pushout.inr_desc _ _ _

omit [HasPushouts C] in
lemma source_compatibility {Y : C}
    {a : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Y}
    {b : SSet.stdSimplex.obj c.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y}
    (sq : CommSq a (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) b) :
    tensorSourceMap D α ≫ homEquiv D s hs B a =
      tensorMap D A c ≫ SSet.yonedaEquiv b := by
  have h := congrArg (homEquiv D s hs A) sq.w
  have hb := homEquiv_presentationMap D s hs A c (SSet.yonedaEquiv b)
  rw [Equiv.symm_apply_apply] at hb
  exact (homEquiv_source_naturality D s hs α a).trans (h.trans hb)

variable [HasTerminal C] {Y : C}
  [HasLiftingProperty (relativeTensorMap D α c) (terminal.from Y)]

def sourceLiftStruct
    {a : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Y}
    {b : SSet.stdSimplex.obj c.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y}
    (sq : CommSq a (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) b) :
    sq.LiftStruct := by
  let d := pushout.desc (homEquiv D s hs B a) (SSet.yonedaEquiv b)
    (source_compatibility D s hs α c sq)
  have q : CommSq d (relativeTensorMap D α c) (terminal.from Y) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  refine ⟨SSet.yonedaEquiv.symm q.lift, ?_, ?_⟩
  · apply (homEquiv D s hs B).injective
    rw [homEquiv_presentationMap]
    exact (inl_relativeTensorMap_assoc D α c q.lift).symm.trans
      ((congrArg (fun k ↦
        pushout.inl (tensorSourceMap D α) (tensorMap D A c) ≫ k) q.fac_left).trans
          (pushout.inl_desc _ _ _))
  · apply SSet.yonedaEquiv.injective
    change α.app c.pt ≫ (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Y))
      ((SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom B).obj Y)).symm q.lift) = _
    rw [Equiv.apply_symm_apply]
    exact (inr_relativeTensorMap_assoc D α c q.lift).symm.trans
      ((congrArg (fun k ↦
        pushout.inr (tensorSourceMap D α) (tensorMap D A c) ≫ k) q.fac_left).trans
          (pushout.inr_desc _ _ _))

lemma source_hasLiftingProperty :
    HasLiftingProperty (presentationMap D s hs c) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y) where
  sq_hasLift sq := CommSq.HasLift.mk' (sourceLiftStruct D s hs α c sq)

end SerrePositivity.HomotopyFunctionComplex.HomPresentation
