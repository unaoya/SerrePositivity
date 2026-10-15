module
public import SerrePositivity.DifferentialGraded.Module.ParamCurry

/-! # 余極限を源とする主Hom endの極限表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Category.{w'} J] [Small.{u} J]

abbrev moduleHomSourceDiagram (F : J ⥤ ModuleCategory A D) (N : ModuleCategory A D) :
    Jᵒᵖ ⥤ Complex A :=
  F.op ⋙ (eHomFunctor (Complex A) (ModuleCategory A D)).flip.obj N

def moduleColimitHomCone {F : J ⥤ ModuleCategory A D} (c : Cocone F)
    (N : ModuleCategory A D) : Cone (moduleHomSourceDiagram A D F N) where
  pt := moduleHom A D (ForgetEnrichment.to (Complex A) c.pt)
    (ForgetEnrichment.to (Complex A) N)
  π :=
    { app := fun j => eHomWhiskerRight (Complex A) (c.ι.app j.unop) N
      naturality := by
        intro i j f
        dsimp
        rw [Category.id_comp]
        change eHomWhiskerRight (Complex A) (c.ι.app j.unop) N =
          eHomWhiskerRight (Complex A) (c.ι.app i.unop) N ≫
            eHomWhiskerRight (Complex A) (F.map f.unop) N
        rw [← eHomWhiskerRight_comp, c.w f.unop] }

def moduleColimitHomUncurryCocone {F : J ⥤ ModuleCategory A D}
    (N : ModuleCategory A D) (s : Cone (moduleHomSourceDiagram A D F N)) :
    Cocone (F ⋙ moduleTensorLeftFunctor A D s.pt) where
  pt := N
  ι :=
    { app := fun j => moduleParamUncurry A D (s.π.app (op j))
      naturality := by
        intro i j f
        dsimp
        rw [Category.comp_id]
        exact (moduleParamUncurry_naturality_source A D (F.map f) (s.π.app (op j))).trans
          (congrArg (moduleParamUncurry A D) (s.w f.op)) }

def moduleColimitHomLift {F : J ⥤ ModuleCategory A D} {c : Cocone F}
    (hc : IsColimit c) (N : ModuleCategory A D)
    (s : Cone (moduleHomSourceDiagram A D F N)) :
    s.pt ⟶ (moduleColimitHomCone A D c N).pt :=
  moduleParamCurry A D ((isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).desc
    (moduleColimitHomUncurryCocone A D N s))

lemma moduleColimitHomLift_π {F : J ⥤ ModuleCategory A D} {c : Cocone F}
    (hc : IsColimit c) (N : ModuleCategory A D)
    (s : Cone (moduleHomSourceDiagram A D F N)) (j : Jᵒᵖ) :
    moduleColimitHomLift A D hc N s ≫ eHomWhiskerRight (Complex A) (c.ι.app j.unop) N =
      s.π.app j := by
  apply moduleParamUncurry_injective A D (M := F.obj j.unop) (N := N)
  have hn := moduleParamUncurry_naturality_source A D (c.ι.app j.unop)
    (moduleColimitHomLift A D hc N s)
  have hu : moduleParamUncurry A D (moduleColimitHomLift A D hc N s) =
      (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).desc
        (moduleColimitHomUncurryCocone A D N s) := moduleParamUncurry_curry A D _
  have hf : moduleTensorLeftMap A D s.pt (c.ι.app j.unop) ≫
      (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).desc
        (moduleColimitHomUncurryCocone A D N s) = moduleParamUncurry A D (s.π.app j) :=
    (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).fac _ j.unop
  exact hn.symm.trans
    ((congrArg (fun b => moduleTensorLeftMap A D s.pt (c.ι.app j.unop) ≫ b) hu).trans hf)

def moduleColimitHomIsLimit {F : J ⥤ ModuleCategory A D} {c : Cocone F}
    (hc : IsColimit c) (N : ModuleCategory A D) :
    IsLimit (moduleColimitHomCone A D c N) where
  lift := moduleColimitHomLift A D hc N
  fac := moduleColimitHomLift_π A D hc N
  uniq s a ha := by
    apply moduleParamUncurry_injective A D (M := c.pt) (N := N)
    unfold moduleColimitHomLift
    rw [moduleParamUncurry_curry]
    apply (isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).hom_ext
    intro j
    have hn := moduleParamUncurry_naturality_source A D (c.ι.app j)
      (show s.pt ⟶ moduleHom A D (ForgetEnrichment.to (Complex A) c.pt)
        (ForgetEnrichment.to (Complex A) N) from a)
    have hj : a ≫ eHomWhiskerRight (Complex A) (c.ι.app j) N = s.π.app (op j) := ha (op j)
    exact (hn.trans (congrArg (moduleParamUncurry A D) hj)).trans
      ((isColimitOfPreserves (moduleTensorLeftFunctor A D s.pt) hc).fac
        (moduleColimitHomUncurryCocone A D N s) j).symm

end SerrePositivity.DifferentialGraded
