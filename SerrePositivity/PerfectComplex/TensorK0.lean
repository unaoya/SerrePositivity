module
public import SerrePositivity.PerfectComplex.TensorSupport
public import SerrePositivity.HomologicalAlgebra.CochainTensorShift
public import SerrePositivity.HomologicalAlgebra.CochainTensorCone
public import SerrePositivity.PerfectComplex.ConeAdditivity
public import SerrePositivity.PerfectComplex.ClosedSupportCongr

/-! # Tensor products on closed-support Grothendieck groups

We use the representative of a homotopy object to define tensor classes.
Isomorphism invariance follows from tensoring homotopy equivalences; cone
additivity follows from the concrete tensor-cone comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
variable {R : Type u} [CommRing R]
variable {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}

/-- The concrete representative of a supported homotopy object. -/
abbrev supportedPerfectRepresentative (X : SupportedPerfectHomotopyOn Y) :
    CochainComplex (ModuleCat.{u} R) ℤ := X.obj.obj.as

lemma supportedPerfectRepresentative_perfect (X : SupportedPerfectHomotopyOn Y) :
    strictlyPerfectComplex R (supportedPerfectRepresentative X) :=
  (perfectHomotopyProperty_quotient R _).mp X.obj.property

lemma supportedPerfectRepresentative_support (X : SupportedPerfectHomotopyOn Y) :
    HasHomologySupportOn Y (supportedPerfectRepresentative X) :=
  (perfectHomotopyObj_supportedOn_iff Y _ (supportedPerfectRepresentative_perfect X)).mp
    X.property

/-- The tensor object, supported in the intersection. -/
def supportedPerfectTensorObj (X : SupportedPerfectHomotopyOn Y)
    (Q : SupportedPerfectHomotopyOn Z) : SupportedPerfectHomotopyOn (Y ⊓ Z) :=
  supportedPerfectOnObj (Y ⊓ Z)
    (cochainTensor (supportedPerfectRepresentative X) (supportedPerfectRepresentative Q))
    (strictlyPerfectComplex_cochainTensor _ _
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Q))
    ((supportedPerfectRepresentative_support X).cochainTensor
      (supportedPerfectRepresentative_support Q)
      (supportedPerfectRepresentative_perfect X) (supportedPerfectRepresentative_perfect Q))

/-- Replacing both representatives by isomorphic homotopy objects preserves the tensor object. -/
def supportedPerfectTensorIso {X X' : SupportedPerfectHomotopyOn Y}
    {Q Q' : SupportedPerfectHomotopyOn Z} (e : X ≅ X') (g : Q ≅ Q') :
    supportedPerfectTensorObj X Q ≅ supportedPerfectTensorObj X' Q' :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (HomotopyCategory.isoOfHomotopyEquiv
      (cochainTensorHomotopyEquiv
        (HomotopyCategory.homotopyEquivOfIso
          ((supportedPerfectOnInclusion Y ⋙ perfectHomotopyInclusion R).mapIso e))
        (HomotopyCategory.homotopyEquivOfIso
          ((supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R).mapIso g)))))

namespace K0WithSupport

/-- The tensor class before descent to either Grothendieck group. -/
def tensorClass (X : SupportedPerfectHomotopyOn Y) (Q : SupportedPerfectHomotopyOn Z) :
    K0WithSupport (Y ⊓ Z) := mk _ (supportedPerfectTensorObj X Q)

lemma tensorClass_iso {X X' : SupportedPerfectHomotopyOn Y}
    {Q Q' : SupportedPerfectHomotopyOn Z} (e : X ≅ X') (g : Q ≅ Q') :
    tensorClass X Q = tensorClass X' Q' := mk_iso _ (supportedPerfectTensorIso e g)

lemma tensorClass_concrete (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (sp : HasHomologySupportOn Y P) (sq : HasHomologySupportOn Z Q) :
    tensorClass (supportedPerfectOnObj Y P hp sp) (supportedPerfectOnObj Z Q hq sq) =
      mk _ (supportedPerfectOnObj (Y ⊓ Z) (cochainTensor P Q)
        (strictlyPerfectComplex_cochainTensor P Q hp hq) (sp.cochainTensor sq hp hq)) := rfl

/-- Tensor classes satisfy the concrete cone relation in their first variable. -/
lemma tensorClass_cone_left (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hp' : strictlyPerfectComplex R P')
    (sp : HasHomologySupportOn Y P) (sp' : HasHomologySupportOn Y P')
    (f : P ⟶ P') (Q : SupportedPerfectHomotopyOn Z) :
    tensorClass (supportedPerfectOnObj Y (CochainComplex.mappingCone f)
      (strictlyPerfectComplex_mappingCone R f hp hp') (sp.mappingCone f sp')) Q =
      tensorClass (supportedPerfectOnObj Y P' hp' sp') Q -
        tensorClass (supportedPerfectOnObj Y P hp sp) Q := by
  let T := supportedPerfectRepresentative Q
  let ht := supportedPerfectRepresentative_perfect Q
  let st := supportedPerfectRepresentative_support Q
  let hpt := strictlyPerfectComplex_cochainTensor P T hp ht
  let hp't := strictlyPerfectComplex_cochainTensor P' T hp' ht
  let spt := sp.cochainTensor st hp ht
  let sp't := sp'.cochainTensor st hp' ht
  have he := mk_iso (Y ⊓ Z) (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    ((homotopyQuot R).mapIso (cochainTensorConeLeft f T))) :
    supportedPerfectTensorObj
      (supportedPerfectOnObj Y (CochainComplex.mappingCone f)
        (strictlyPerfectComplex_mappingCone R f hp hp') (sp.mappingCone f sp')) Q ≅
      supportedPerfectOnObj (Y ⊓ Z) (CochainComplex.mappingCone (cochainTensorMap f (𝟙 T)))
        (strictlyPerfectComplex_mappingCone R _ hpt hp't) (spt.mappingCone _ sp't))
  change mk _ _ = _
  rw [he]
  exact mk_cone (Y ⊓ Z) (cochainTensor P T) (cochainTensor P' T)
    hpt hp't spt sp't (cochainTensorMap f (𝟙 T))

/-- Fixing a supported perfect complex on the right gives an additive map from K₀. -/
def tensorWithRight (Q : SupportedPerfectHomotopyOn Z) :
    K0WithSupport Y →+ K0WithSupport (Y ⊓ Z) :=
  lift Y (fun X => tensorClass X Q)
    (fun e => tensorClass_iso e (Iso.refl Q))
    (closedSupport_triangleAdditive_of_cone Y (fun X => tensorClass X Q)
      (fun e => tensorClass_iso e (Iso.refl Q))
      (fun P P' hp hp' sp sp' f => tensorClass_cone_left P P' hp hp' sp sp' f Q))

@[simp]
lemma tensorWithRight_mk (X : SupportedPerfectHomotopyOn Y) (Q : SupportedPerfectHomotopyOn Z) :
    tensorWithRight Q (mk Y X) = tensorClass X Q := by
  simp only [tensorWithRight, lift_mk]

/-- Symmetry of tensor classes, transported along equality of closed intersections. -/
lemma tensorClass_comm (X : SupportedPerfectHomotopyOn Y) (Q : SupportedPerfectHomotopyOn Z) :
    congr (inf_comm Y Z) (tensorClass X Q) = tensorClass Q X := by
  rw [tensorClass, congr_mk]
  have e : (supportedPerfectOnCongr (inf_comm Y Z) (supportedPerfectTensorObj X Q)).obj.obj ≅
      (supportedPerfectTensorObj Q X).obj.obj := by
    rw [supportedPerfectOnCongr_obj]
    exact (homotopyQuot R).mapIso (cochainTensorSymmetry
      (supportedPerfectRepresentative X) (supportedPerfectRepresentative Q))
  exact mk_iso _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e))

/-- Fixing a supported perfect complex on the left also gives an additive map. -/
def tensorWithLeft (X : SupportedPerfectHomotopyOn Y) :
    K0WithSupport Z →+ K0WithSupport (Y ⊓ Z) :=
  (congr (inf_comm Z Y)).toAddMonoidHom.comp (tensorWithRight X)

@[simp]
lemma tensorWithLeft_mk (X : SupportedPerfectHomotopyOn Y) (Q : SupportedPerfectHomotopyOn Z) :
    tensorWithLeft X (mk Z Q) = tensorClass X Q := by
  simp only [tensorWithLeft, AddMonoidHom.comp_apply, tensorWithRight_mk]
  exact tensorClass_comm Q X

/-- The first-variable homomorphism is additive on triangles in its fixed right object. -/
lemma tensorWithRight_triangle (T : Triangle (SupportedPerfectHomotopyOn Z))
    (hT : T ∈ distTriang _) :
    (tensorWithRight T.obj₂ : K0WithSupport Y →+ K0WithSupport (Y ⊓ Z)) =
      tensorWithRight T.obj₁ + tensorWithRight T.obj₃ := by
  apply hom_ext
  intro X
  simp only [AddMonoidHom.add_apply, tensorWithRight_mk]
  rw [← tensorWithLeft_mk X T.obj₂, ← tensorWithLeft_mk X T.obj₁,
    ← tensorWithLeft_mk X T.obj₃, mk_triangle Z T hT, map_add]

/-- The cup product, additive in both arguments and supported in their intersection. -/
def cup : K0WithSupport Y →+ K0WithSupport Z →+ K0WithSupport (Y ⊓ Z) := by
  let F : K0WithSupport Z →+ K0WithSupport Y →+ K0WithSupport (Y ⊓ Z) :=
    lift Z tensorWithRight
      (fun e => by
        apply hom_ext
        intro X
        simp only [tensorWithRight_mk]
        exact tensorClass_iso (Iso.refl X) e)
      (fun T hT => tensorWithRight_triangle T hT)
  exact F.flip

@[simp]
lemma cup_mk_mk (X : SupportedPerfectHomotopyOn Y) (Q : SupportedPerfectHomotopyOn Z) :
    cup (mk Y X) (mk Z Q) = tensorClass X Q := by
  simp only [cup, AddMonoidHom.flip_apply, lift_mk, tensorWithRight_mk]

lemma cup_add_left (x x' : K0WithSupport Y) (y : K0WithSupport Z) :
    cup (x + x') y = cup x y + cup x' y := by
  rw [map_add, AddMonoidHom.add_apply]

lemma cup_add_right (x : K0WithSupport Y) (y y' : K0WithSupport Z) :
    cup x (y + y') = cup x y + cup x y' := (cup x).map_add y y'

@[simp] lemma cup_zero_left (y : K0WithSupport Z) :
    cup (0 : K0WithSupport Y) y = 0 := by
  rw [map_zero, AddMonoidHom.zero_apply]

@[simp] lemma cup_zero_right (x : K0WithSupport Y) :
    cup x (0 : K0WithSupport Z) = 0 := (cup x).map_zero

/-- Equality of bilinear pairings is detected on pairs of supported complexes. -/
lemma cupPairing_hom_ext {B : Type*} [AddCommGroup B]
    {f g : K0WithSupport Y →+ K0WithSupport Z →+ B}
    (h : ∀ X Q, f (mk Y X) (mk Z Q) = g (mk Y X) (mk Z Q)) : f = g := by
  apply hom_ext
  intro X
  apply hom_ext
  intro Q
  exact h X Q

/-- Commutativity of the cup product, including the equality of its support. -/
lemma cup_comm (x : K0WithSupport Y) (y : K0WithSupport Z) :
    congr (inf_comm Y Z) (cup x y) = cup y x := by
  have he :
      (cup (Y := Y) (Z := Z)).compr₂ (congr (inf_comm Y Z)).toAddMonoidHom =
        (cup (Y := Z) (Z := Y)).flip := by
    apply cupPairing_hom_ext
    intro X Q
    change congr (inf_comm Y Z) (cup (mk Y X) (mk Z Q)) = cup (mk Z Q) (mk Y X)
    rw [cup_mk_mk, cup_mk_mk]
    exact tensorClass_comm X Q
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

/-- Associativity of cup products, transported along associativity of closed intersections. -/
lemma cup_assoc {W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (x : K0WithSupport Y) (y : K0WithSupport Z) (z : K0WithSupport W) :
    congr (inf_assoc Y Z W) (cup (cup x y) z) = cup x (cup y z) := by
  let lhs : K0WithSupport Y →+ K0WithSupport Z →+ K0WithSupport W →+
      K0WithSupport (Y ⊓ (Z ⊓ W)) :=
    (cup (Y := Y) (Z := Z)).compr₂
      ((cup (Y := Y ⊓ Z) (Z := W)).compr₂ (congr (inf_assoc Y Z W)).toAddMonoidHom)
  let rhs : K0WithSupport Y →+ K0WithSupport Z →+ K0WithSupport W →+
      K0WithSupport (Y ⊓ (Z ⊓ W)) :=
    (AddMonoidHom.compHom.compl₂ (cup (Y := Z) (Z := W))).comp
        (cup (Y := Y) (Z := Z ⊓ W))
  have he : lhs = rhs := by
    apply hom_ext
    intro X
    apply hom_ext
    intro Q
    apply hom_ext
    intro T
    change congr (inf_assoc Y Z W) (cup (cup (mk Y X) (mk Z Q)) (mk W T)) =
      cup (mk Y X) (cup (mk Z Q) (mk W T))
    simp only [cup_mk_mk, tensorClass, congr_mk]
    have e :
        (supportedPerfectOnCongr (inf_assoc Y Z W)
          (supportedPerfectTensorObj (supportedPerfectTensorObj X Q) T)).obj.obj ≅
        (supportedPerfectTensorObj X (supportedPerfectTensorObj Q T)).obj.obj := by
      rw [supportedPerfectOnCongr_obj]
      exact (homotopyQuot R).mapIso (cochainTensorAssociator
        (supportedPerfectRepresentative X) (supportedPerfectRepresentative Q)
        (supportedPerfectRepresentative T))
    exact mk_iso _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e))
  exact DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun he x) y) z
end K0WithSupport
end SerrePositivity
