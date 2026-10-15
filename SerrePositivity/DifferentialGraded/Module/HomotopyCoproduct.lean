module
public import SerrePositivity.DifferentialGraded.Module.CoproductHom
public import SerrePositivity.DifferentialGraded.Module.HomCycles
public import SerrePositivity.DifferentialGraded.Complexes.ProductAcyclic

/-! # 余積からの加群ホモトピーの成分判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

lemma moduleHomCycle_precompose {M N T : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ T) :
    (eHomWhiskerRight (Complex A) f T).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ g))).val := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π, ← moduleEvaluation_cochain A D x g,
    ← moduleEvaluation_cochain A D x (f ≫ g), CategoryTheory.Functor.map_comp,
    Cochain.ofHom_comp]

private def productElement (F : J → Complex A) (n : ℤ) (z : ∀ j, (F j).X n) :
    (∏ᶜ F).X n :=
  (Fan.IsLimit.lift (complexProductDegreeIsLimit A F n)
    (fun j => moduleElementMap A _ (z j))) (1 : A)

private lemma productElement_π (F : J → Complex A) (n : ℤ) (z : ∀ j, (F j).X n) (j : J) :
    (Pi.π F j).f n (productElement A F n z) = z j := by
  have h := congrArg (fun a => a (1 : A))
    (Fan.IsLimit.fac (complexProductDegreeIsLimit A F n)
      (fun j => moduleElementMap A _ (z j)) j)
  change (Pi.π F j).f n (productElement A F n z) = (1 : A) • z j at h
  simpa only [one_smul] using h

private lemma productElement_ext (F : J → Complex A) (n : ℤ) (a b : (∏ᶜ F).X n)
    (h : ∀ j, (Pi.π F j).f n a = (Pi.π F j).f n b) : a = b := by
  have hm : moduleElementMap A _ a = moduleElementMap A _ b := by
    apply complexProductDegree_hom_ext A F n
    intro j
    apply (moduleElementEquiv A _).injective
    change (Pi.π F j).f n ((1 : A) • a) = (Pi.π F j).f n ((1 : A) • b)
    simpa only [one_smul] using h j
  exact (moduleElementEquiv A _).symm.injective hm

lemma moduleCoproduct_homotopy_of_components (M : J → ModuleCategory A D)
    {N : ModuleCategory A D} (f g : ∐ M ⟶ N)
    (h : ∀ j, Nonempty (ModuleHomotopy A D (Sigma.ι M j ≫ f) (Sigma.ι M j ≫ g))) :
    Nonempty (ModuleHomotopy A D f g) := by
  let F := moduleCoproductHomFamily A D M N
  let e := moduleCoproductHomIso A D M N
  let hj := fun j => Classical.choice (h j)
  let t := productElement A F (-1) (fun j => (hj j).val)
  let b := e.inv.f (-1) t
  have hb (j : J) : (eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f (-1) b = (hj j).val := by
    have he := congrArg (fun a => a.f (-1)) (moduleCoproductHomIso_hom_π A D M N j)
    have hi := congrArg (fun a => a.f (-1)) e.inv_hom_id
    have ht : e.hom.f (-1) b = t := congrArg (fun a => a t) hi
    calc
      _ = (Pi.π F j).f (-1) (e.hom.f (-1) b) := (congrArg (fun a => a b) he).symm
      _ = (Pi.π F j).f (-1) t := congrArg ((Pi.π F j).f (-1)) ht
      _ = _ := productElement_π A F (-1) _ j
  refine ⟨⟨b, ?_⟩⟩
  let C := moduleHom A D (ForgetEnrichment.to (Complex A) (show ModuleCategory A D from ∐ M))
    (ForgetEnrichment.to (Complex A) N)
  let zf := (cycleFromUnit C (ForgetEnrichment.homTo (Complex A) f)).val
  let zg := (cycleFromUnit C (ForgetEnrichment.homTo (Complex A) g)).val
  change C.d (-1) 0 b = zf - zg
  have hi : Function.Injective (e.hom.f 0) := by
    intro a b hab
    have he := congrArg (fun a => a.f 0) e.hom_inv_id
    have ha := congrArg (fun k => k a) he
    have hb := congrArg (fun k => k b) he
    exact ha.symm.trans ((congrArg (e.inv.f 0) hab).trans hb)
  apply hi
  apply productElement_ext A F 0
  intro j
  have he := congrArg (fun a => a.f 0) (moduleCoproductHomIso_hom_π A D M N j)
  have he' (a : C.X 0) : (Pi.π F j).f 0 (e.hom.f 0 a) =
      (eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f 0 a := congrArg (fun k => k a) he
  rw [he', he']
  have hc := congrArg (fun k => k b)
    ((eHomWhiskerRight (Complex A) (Sigma.ι M j) N).comm (-1) 0)
  change (F j).d (-1) 0
      ((eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f (-1) b) =
    (eHomWhiskerRight (Complex A) (Sigma.ι M j) N).f 0 (C.d (-1) 0 b) at hc
  have hd : (F j).d (-1) 0 (hj j).val =
      (cycleFromUnit (F j) (ForgetEnrichment.homTo (Complex A) (Sigma.ι M j ≫ f))).val -
        (cycleFromUnit (F j) (ForgetEnrichment.homTo (Complex A) (Sigma.ι M j ≫ g))).val :=
    (hj j).property
  rw [← hc, hb, hd, map_sub]
  exact congrArg₂ (fun a b => a - b)
    (moduleHomCycle_precompose A D (Sigma.ι M j) f).symm
    (moduleHomCycle_precompose A D (Sigma.ι M j) g).symm

end SerrePositivity.DifferentialGraded
