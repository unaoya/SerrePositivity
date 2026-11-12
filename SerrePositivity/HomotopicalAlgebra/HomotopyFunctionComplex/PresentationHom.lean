module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Simplicial Hom on a presentation by standard simplices

A map from a colimit of standard simplices to `Hom(A,Y)` is exactly a
cocone of the corresponding objects of A with vertex Y. Only the particular
colimit in C is needed, so finite presentations work in finite-cocomplete C.
-/

@[expose] public section
universe v u w t
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.HomPresentation
variable {C : Type u} [Category.{v} C] {I : Type w} [Category.{t} I]
  (D : I ⥤ SimplexCategory) (s : Cocone (D ⋙ SSet.stdSimplex.{v}))
  (hs : IsColimit s) (A : SimplexCategory ⥤ C) {Y : C}

def toCocone (f : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) :
    D ⋙ A ⟶ (Functor.const I).obj Y where
  app i := SSet.yonedaEquiv (s.ι.app i ≫ f)
  naturality i k φ := by
    change A.map (D.map φ) ≫ SSet.yonedaEquiv (s.ι.app k ≫ f) =
      SSet.yonedaEquiv (s.ι.app i ≫ f) ≫ 𝟙 Y
    rw [Category.comp_id]
    have h := SSet.yonedaEquiv_naturality (D.map φ) (s.ι.app k ≫ f)
    change A.map (D.map φ) ≫ SSet.yonedaEquiv (s.ι.app k ≫ f) = _ at h
    have hw : SSet.stdSimplex.map (D.map φ) ≫ s.ι.app k = s.ι.app i :=
      s.w φ
    exact h.trans (congrArg SSet.yonedaEquiv
      ((Category.assoc _ _ _).symm.trans (congrArg (fun g ↦ g ≫ f) hw)))

abbrev simplexCocone (τ : D ⋙ A ⟶ (Functor.const I).obj Y) :
    Cocone (D ⋙ SSet.stdSimplex.{v}) where
  pt := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y
  ι :=
    { app i := (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm (τ.app i)
      naturality i k φ := by
        change SSet.stdSimplex.map (D.map φ) ≫
            (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm (τ.app k) =
          (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm (τ.app i) ≫ 𝟙 _
        rw [Category.comp_id, SSet.yonedaEquiv_symm_naturality_left]
        apply congrArg (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm
        exact (τ.naturality φ).trans (Category.comp_id _) }

def fromCocone (τ : D ⋙ A ⟶ (Functor.const I).obj Y) :
    s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y := hs.desc (simplexCocone D A τ)

@[reassoc (attr := simp)]
lemma ι_fromCocone (τ : D ⋙ A ⟶ (Functor.const I).obj Y) (i : I) :
    s.ι.app i ≫ fromCocone D s hs A τ =
      (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm (τ.app i) :=
  hs.fac (simplexCocone D A τ) i

def coconeEquiv : (s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃
    (D ⋙ A ⟶ (Functor.const I).obj Y) where
  toFun := toCocone D s A
  invFun := fromCocone D s hs A
  left_inv f := by
    apply hs.hom_ext
    intro i
    rw [ι_fromCocone]
    exact SSet.yonedaEquiv.symm_apply_apply _
  right_inv τ := by
    apply NatTrans.ext
    funext i
    change SSet.yonedaEquiv (s.ι.app i ≫ fromCocone D s hs A τ) = τ.app i
    rw [ι_fromCocone, Equiv.apply_symm_apply]

def homEquiv [HasColimit (D ⋙ A)] :
    (s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃ (colimit (D ⋙ A) ⟶ Y) :=
  (coconeEquiv D s hs A).trans (colimit.isColimit (D ⋙ A)).homEquiv.symm

@[reassoc (attr := simp)]
lemma ι_homEquiv [HasColimit (D ⋙ A)] (f : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) (i : I) :
    colimit.ι (D ⋙ A) i ≫ homEquiv D s hs A f = SSet.yonedaEquiv (s.ι.app i ≫ f) :=
  colimit.ι_desc _ _

lemma homEquiv_naturality [HasColimit (D ⋙ A)] {Z : C}
    (f : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) (p : Y ⟶ Z) :
    homEquiv D s hs A (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) = homEquiv D s hs A f ≫ p := by
  apply colimit.hom_ext
  intro i
  rw [ι_homEquiv]
  calc
    _ = SSet.yonedaEquiv (s.ι.app i ≫ f) ≫ p := rfl
    _ = (colimit.ι (D ⋙ A) i ≫ homEquiv D s hs A f) ≫ p :=
      congrArg (fun g ↦ g ≫ p) (ι_homEquiv D s hs A f i).symm
    _ = _ := Category.assoc _ _ _

def presentationMap (c : Cocone D) : s.pt ⟶ SSet.stdSimplex.obj c.pt :=
  hs.desc (SSet.stdSimplex.mapCocone c)

abbrev tensorMap [HasColimit (D ⋙ A)] (c : Cocone D) : colimit (D ⋙ A) ⟶ A.obj c.pt :=
  colimit.desc _ (A.mapCocone c)

lemma homEquiv_presentationMap [HasColimit (D ⋙ A)] (c : Cocone D) (h : A.obj c.pt ⟶ Y) :
    homEquiv D s hs A (presentationMap D s hs c ≫
      (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm h) = tensorMap D A c ≫ h := by
  apply colimit.hom_ext
  intro i
  rw [ι_homEquiv, ← Category.assoc, ← Category.assoc, colimit.ι_desc]
  have hw : s.ι.app i ≫ presentationMap D s hs c = SSet.stdSimplex.map (c.ι.app i) :=
    hs.fac (SSet.stdSimplex.mapCocone c) i
  rw [hw, ← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.HomotopyFunctionComplex.HomPresentation
