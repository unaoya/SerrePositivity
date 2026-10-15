module
public import SerrePositivity.DifferentialGraded.Derived.ResolutionHom
public import SerrePositivity.DifferentialGraded.Module.HomotopyCoproductUniversal

/-! # 射影解像度から構成する導来加群圏の余積 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

lemma moduleProjectiveDerivedHomEquiv_precompose {P Q N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P)
    (hQ : moduleHomotopicallyProjective A D Q) (f : P ⟶ Q)
    (g : (moduleToHomotopy A D).obj Q ⟶ (moduleToHomotopy A D).obj N) :
    (moduleToDerived A D).map f ≫ moduleProjectiveDerivedHomEquiv A D hQ N g =
      moduleProjectiveDerivedHomEquiv A D hP N ((moduleToHomotopy A D).map f ≫ g) := by
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  rw [← CategoryTheory.Functor.map_comp, moduleProjectiveDerivedHomEquiv_map,
    moduleProjectiveDerivedHomEquiv_map, CategoryTheory.Functor.map_comp]

def moduleProjectiveDerivedCofan (M : J → ModuleCategory A D) :
    Cofan (fun j => (moduleToDerived A D).obj (M j)) :=
  Cofan.mk ((moduleToDerived A D).obj (∐ M))
    (fun j => (moduleToDerived A D).map (Sigma.ι M j))

def moduleProjectiveDerivedCofanDesc (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (s : Cofan (fun j => (moduleToDerived A D).obj (M j))) :
    (moduleToDerived A D).obj (∐ M) ⟶ s.pt :=
  moduleProjectiveDerivedHomEquiv A D (moduleCoproduct_homotopicallyProjective A D M hM)
    s.pt.as.obj
    (moduleHomotopyCofanDesc A D M
      (Cofan.mk ((moduleToHomotopy A D).obj s.pt.as.obj) (fun j =>
        (moduleProjectiveDerivedHomEquiv A D (hM j) s.pt.as.obj).symm (s.inj j))))

lemma moduleProjectiveDerivedCofanDesc_fac (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (s : Cofan (fun j => (moduleToDerived A D).obj (M j))) (j : J) :
    (moduleToDerived A D).map (Sigma.ι M j) ≫
      moduleProjectiveDerivedCofanDesc A D M hM s = s.inj j := by
  unfold moduleProjectiveDerivedCofanDesc
  rw [moduleProjectiveDerivedHomEquiv_precompose A D (hM j)
    (moduleCoproduct_homotopicallyProjective A D M hM), moduleHomotopyCofanDesc_fac]
  exact (moduleProjectiveDerivedHomEquiv A D (hM j) s.pt.as.obj).apply_symm_apply _

lemma moduleProjectiveDerivedCoproduct_hom_ext (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    {N : DerivedModuleCategory A D} {f g : (moduleToDerived A D).obj (∐ M) ⟶ N}
    (h : ∀ j, (moduleToDerived A D).map (Sigma.ι M j) ≫ f =
      (moduleToDerived A D).map (Sigma.ι M j) ≫ g) : f = g := by
  let e := moduleProjectiveDerivedHomEquiv A D
    (moduleCoproduct_homotopicallyProjective A D M hM) N.as.obj
  obtain ⟨f, rfl⟩ := e.surjective f
  obtain ⟨g, rfl⟩ := e.surjective g
  apply congrArg e
  apply moduleHomotopyCoproduct_hom_ext A D M
  intro j
  apply (moduleProjectiveDerivedHomEquiv A D (hM j) N.as.obj).injective
  exact (moduleProjectiveDerivedHomEquiv_precompose A D (hM j)
    (moduleCoproduct_homotopicallyProjective A D M hM) (Sigma.ι M j) f).symm.trans
      ((h j).trans (moduleProjectiveDerivedHomEquiv_precompose A D (hM j)
        (moduleCoproduct_homotopicallyProjective A D M hM) (Sigma.ι M j) g))

def moduleProjectiveDerivedCofanIsColimit (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    IsColimit (moduleProjectiveDerivedCofan A D M) :=
  Cofan.IsColimit.mk _ (moduleProjectiveDerivedCofanDesc A D M hM)
    (moduleProjectiveDerivedCofanDesc_fac A D M hM) (by
      intro s m hm
      apply moduleProjectiveDerivedCoproduct_hom_ext A D M hM
      intro j
      exact (hm j).trans (moduleProjectiveDerivedCofanDesc_fac A D M hM s j).symm)

/-- 任意のu-smallな導来対象族に対する余積。 -/
instance moduleDerivedHasCoproductsOfShape :
    HasColimitsOfShape (Discrete J) (DerivedModuleCategory A D) where
  has_colimit F := by
    let R := fun j : J => moduleCanonicalProjectiveResolution A D (F.obj ⟨j⟩).as.obj
    let P := fun j : J => (R j).obj
    have : HasColimit (Discrete.functor (fun j => (moduleToDerived A D).obj (P j))) :=
      ⟨⟨moduleProjectiveDerivedCofan A D P,
        moduleProjectiveDerivedCofanIsColimit A D P (fun j => (R j).projective)⟩⟩
    let e : Discrete.functor (fun j => (moduleToDerived A D).obj (P j)) ≅ F :=
      Discrete.natIso (fun j => moduleDerivedIso A D (R j.as).π (R j.as).quasiIso)
    exact hasColimit_of_iso e.symm

end SerrePositivity.DifferentialGraded
