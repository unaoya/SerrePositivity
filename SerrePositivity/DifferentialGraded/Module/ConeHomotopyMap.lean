module
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
public import SerrePositivity.DifferentialGraded.Module.HomotopyCoproduct

/-! # ホモトピーまで可換なsquareによるcone射 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定された主Homの要素をそのまま複体のホモトピーへ移す。 -/
def moduleHomotopyComponent {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) :
    Homotopy ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map g) := by
  let z := (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x).f (-1) h.val
  have hd := congrArg ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x).f 0) h.property
  change (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x).f 0
      ((moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N)).d (-1) 0 h.val) = _ at hd
  rw [moduleHomElement_d_π, map_sub, ← moduleEvaluation_cochain,
    ← moduleEvaluation_cochain] at hd
  exact (Cochain.equivHomotopy _ _).symm ⟨z, (sub_eq_iff_eq_add).1 hd.symm⟩

lemma moduleHomotopyComponent_cochain {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) :
    ((Cochain.equivHomotopy _ _) (moduleHomotopyComponent A D h x)).val =
      (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) x).f (-1) h.val :=
  congrArg Subtype.val ((Cochain.equivHomotopy _ _).apply_symm_apply _)

/-- squareの両辺を評価した合成で表示する。ホモトピーの成分は変更しない。 -/
def moduleHomotopySquareComponent {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) (x : D) :
    Homotopy ((moduleEvaluation A D x).map f ≫ (moduleEvaluation A D x).map v)
      ((moduleEvaluation A D x).map u ≫ (moduleEvaluation A D x).map g) where
  hom := (moduleHomotopyComponent A D h x).hom
  zero := (moduleHomotopyComponent A D h x).zero
  comm p := by
    simpa only [CategoryTheory.Functor.map_comp] using (moduleHomotopyComponent A D h x).comm p

/-- cone射の左入力。hの符号はd h = f≫v − u≫gの規約に従う。 -/
def moduleConeHomotopyInput {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).X (-1) :=
  (eHomWhiskerRight (Complex A) u (moduleCone A D g)).f (-1) (moduleConeInlElement A D g) +
    (eHomWhiskerLeft (Complex A) M (moduleConeInr A D g)).f (-1) h.val

lemma moduleConeHomotopyInput_π {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g)) x).f (-1)
        (moduleConeHomotopyInput A D f g u v h) =
      (Cochain.ofHom ((moduleEvaluation A D x).map u)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map g)) (zero_add _) +
      (show Cochain ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj N') (-1)
        from (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N') x).f (-1) h.val).comp
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map g))) (add_zero _) := by
  rw [moduleConeHomotopyInput, map_add, moduleHomWhiskerRight_apply_π,
    moduleConeInlElement_π, moduleHomWhiskerLeft_apply_π, moduleConeInr_eval]

lemma moduleConeHomotopyInput_d {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeHomotopyInput A D f g u v h) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (f ≫ (v ≫ moduleConeInr A D g)))).val := by
  let r := eHomWhiskerRight (Complex A) u (moduleCone A D g)
  let l := eHomWhiskerLeft (Complex A) M (moduleConeInr A D g)
  have hr := congrArg (fun k => k (moduleConeInlElement A D g)) (r.comm (-1) 0)
  have hl := congrArg (fun k => k h.val) (l.comm (-1) 0)
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
      (r.f (-1) (moduleConeInlElement A D g)) =
    r.f 0 ((moduleHom A D (ForgetEnrichment.to (Complex A) M')
      (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
        (moduleConeInlElement A D g)) at hr
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0 (l.f (-1) h.val) =
    l.f 0 ((moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N')).d (-1) 0 h.val) at hl
  have hh : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N')).d (-1) 0 h.val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (f ≫ v))).val -
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (u ≫ g))).val := h.property
  rw [moduleConeInlElement_d] at hr
  rw [hh, map_sub] at hl
  change (moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D g))).d (-1) 0
      (r.f (-1) (moduleConeInlElement A D g) + l.f (-1) h.val) = _
  rw [map_add, hr, hl]
  dsimp only [r, l]
  rw [moduleHomCycle_precompose, moduleHomCycle_postcompose, moduleHomCycle_postcompose,
    Category.assoc, Category.assoc]
  abel

/-- ホモトピーまで可換なsquareを全dg自然なcone射に延長する。 -/
def moduleConeMapOfHomotopy {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleCone A D f ⟶ moduleCone A D g :=
  moduleConeDescOfBoundary A D f (moduleConeHomotopyInput A D f g u v h)
    (v ≫ moduleConeInr A D g) (moduleConeHomotopyInput_d A D f g u v h)

@[reassoc] lemma moduleConeMapOfHomotopy_inr {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleConeInr A D f ≫ moduleConeMapOfHomotopy A D f g u v h = v ≫ moduleConeInr A D g :=
  moduleConeDescOfBoundary_inr A D _ _ _ _


@[simp] lemma moduleConeMapOfHomotopy_eval {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) (x : D) :
    (moduleEvaluation A D x).map (moduleConeMapOfHomotopy A D f g u v h) =
      mappingCone.mapOfHomotopy
        (moduleHomotopySquareComponent A D f g u v h x) := by
  unfold moduleConeMapOfHomotopy
  rw [moduleConeDescOfBoundary_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_desc]
  unfold mappingCone.mapOfHomotopy
  rw [mappingCone.ofHom_desc]
  rw [moduleConeHomotopyInput_π, CategoryTheory.Functor.map_comp, moduleConeInr_eval]
  have hc : ((Cochain.equivHomotopy _ _)
      (moduleHomotopySquareComponent A D f g u v h x)).val =
      (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N') x).f (-1) h.val :=
    moduleHomotopyComponent_cochain A D h x
  rw [hc]

@[reassoc] lemma moduleConeMapOfHomotopy_connecting {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleConeConnecting A D f ≫ u⟦(1 : ℤ)⟧' =
      moduleConeMapOfHomotopy A D f g u v h ≫ moduleConeConnecting A D g := by
  apply moduleMorphism_ext
  intro x
  simp only [CategoryTheory.Functor.map_comp, moduleConeConnecting_eval,
    moduleConeMapOfHomotopy_eval, moduleShiftFunctor_eq, moduleShiftFunctor_map_eval]
  exact (mappingCone.triangleMapOfHomotopy_comm₃ _).symm

end SerrePositivity.DifferentialGraded
