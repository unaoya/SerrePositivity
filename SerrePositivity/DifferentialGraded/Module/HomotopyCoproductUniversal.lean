module
public import SerrePositivity.DifferentialGraded.Module.HomotopyCoproduct

/-! # K(D)のu-small余積と商関手による余積の保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

lemma moduleHomotopyCoproduct_hom_ext (M : J → ModuleCategory A D)
    {N : ModuleHomotopyCategory A D}
    {f g : (moduleToHomotopy A D).obj (∐ M) ⟶ N}
    (h : ∀ j, (moduleToHomotopy A D).map (Sigma.ι M j) ≫ f =
      (moduleToHomotopy A D).map (Sigma.ι M j) ≫ g) : f = g := by
  obtain ⟨N⟩ := N
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  apply (moduleToHomotopy_map_eq_iff A D f g).2
  apply moduleCoproduct_homotopy_of_components A D M f g
  intro j
  apply (moduleToHomotopy_map_eq_iff A D _ _).1
  simpa only [CategoryTheory.Functor.map_comp] using h j

def moduleHomotopyCofan (M : J → ModuleCategory A D) :
    Cofan (fun j => (moduleToHomotopy A D).obj (M j)) :=
  Cofan.mk ((moduleToHomotopy A D).obj (∐ M))
    (fun j => (moduleToHomotopy A D).map (Sigma.ι M j))

def moduleHomotopyCofanDesc (M : J → ModuleCategory A D)
    (s : Cofan (fun j => (moduleToHomotopy A D).obj (M j))) :
    (moduleToHomotopy A D).obj (∐ M) ⟶ s.pt :=
  (moduleToHomotopy A D).map (Sigma.desc (fun j =>
    (moduleToHomotopy A D).preimage (X := M j) (Y := s.pt.as) (s.inj j)))

lemma moduleHomotopyCofanDesc_fac (M : J → ModuleCategory A D)
    (s : Cofan (fun j => (moduleToHomotopy A D).obj (M j))) (j : J) :
    (moduleToHomotopy A D).map (Sigma.ι M j) ≫ moduleHomotopyCofanDesc A D M s = s.inj j := by
  unfold moduleHomotopyCofanDesc
  rw [← CategoryTheory.Functor.map_comp, Sigma.ι_comp_desc]
  exact (moduleToHomotopy A D).map_preimage _

def moduleHomotopyCofanIsColimit (M : J → ModuleCategory A D) :
    IsColimit (moduleHomotopyCofan A D M) :=
  Cofan.IsColimit.mk _ (moduleHomotopyCofanDesc A D M)
    (moduleHomotopyCofanDesc_fac A D M) (by
      intro s m hm
      apply moduleHomotopyCoproduct_hom_ext A D M
      intro j
      exact (hm j).trans (moduleHomotopyCofanDesc_fac A D M s j).symm)

instance moduleHomotopyHasCoproductsOfShape :
    HasColimitsOfShape (Discrete J) (ModuleHomotopyCategory A D) where
  has_colimit F := by
    let M : J → ModuleCategory A D := fun j => (F.obj ⟨j⟩).as
    have : HasColimit (Discrete.functor (fun j => (moduleToHomotopy A D).obj (M j))) :=
      ⟨⟨moduleHomotopyCofan A D M, moduleHomotopyCofanIsColimit A D M⟩⟩
    let e : Discrete.functor (fun j => (moduleToHomotopy A D).obj (M j)) ≅ F :=
      Discrete.natIso (fun j => Iso.refl (F.obj j))
    exact hasColimit_of_iso e.symm


instance moduleToHomotopyPreservesCoproduct (M : J → ModuleCategory A D) :
    PreservesColimit (Discrete.functor M) (moduleToHomotopy A D) := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct M)
  exact (isColimitMapCoconeCofanMkEquiv (moduleToHomotopy A D) M _).symm
    (moduleHomotopyCofanIsColimit A D M)

end SerrePositivity.DifferentialGraded
