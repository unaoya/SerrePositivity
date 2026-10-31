module

public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.ClosedSupport.K0
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange
public import SerrePositivity.CommutativeAlgebra.Support.Closed
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.HomologicalAlgebra.Complex.Truncation

/-! # 閉台の K₀ のカップ積

## 概要

閉集合に台を持つ K₀ のテンソル積（カップ積）`K0WithSupport.cup` をホモトピー対象の代表で定め、台の拡大・基底変更との可換性を示す。非輪状な複体と有界平坦複体のテンソルの扱い（台が空なら非輪状）も与える。

## 方針

同型での不変性と写像錐との両立から K₀ へ降ろす。

## 規約

代表の取り方によらないことを示してから定義する。

## 使われ方

KTheory/Adams のテンソル冪と Adams 作用素。
-/

@[expose] public noncomputable section

universe u

section TensorK0Part

set_option backward.isDefEq.respectTransparency false
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

end K0WithSupport
end SerrePositivity

end TensorK0Part

section TensorEnlargePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]
namespace K0WithSupport
variable {Y Y' Z Z' : TopologicalSpace.Closeds (PrimeSpectrum R)}

/-- Enlarge both supports before or after taking the cup product. -/
lemma cup_enlarge (hY : Y ≤ Y') (hZ : Z ≤ Z') (x : K0WithSupport Y) (y : K0WithSupport Z) :
    enlarge (inf_le_inf hY hZ) (cup x y) = cup (enlarge hY x) (enlarge hZ y) := by
  have he :
      (cup (Y := Y) (Z := Z)).compr₂ (enlarge (inf_le_inf hY hZ)) =
        ((cup (Y := Y') (Z := Z')).compl₂ (enlarge hZ)).comp (enlarge hY) := by
    apply cupPairing_hom_ext
    intro X Q
    change enlarge (inf_le_inf hY hZ) (cup (mk Y X) (mk Z Q)) =
      cup (enlarge hY (mk Y X)) (enlarge hZ (mk Z Q))
    simp only [cup_mk_mk, tensorClass, enlarge_mk]
    rfl
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y

end K0WithSupport
end SerrePositivity

end TensorEnlargePart

section TensorBaseChangePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open Functor.Monoidal Functor.OplaxMonoidal
variable {R S : Type u} [CommRing R] [CommRing S]
variable (φ : R →+* S) (P Q : CochainComplex (ModuleCat.{u} R) ℤ)

namespace K0WithSupport
/-- Cup products commute with ring change, even when the target supports are enlarged. -/
lemma cup_map {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {W V : TopologicalSpace.Closeds (PrimeSpectrum S)}
    (hY : supportPullback φ Y ≤ W) (hZ : supportPullback φ Z ≤ V)
    (x : K0WithSupport Y) (y : K0WithSupport Z) :
    map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ) (cup x y) =
      cup (map φ Y W hY x) (map φ Z V hZ y) := by
  have he :
      (cup (Y := Y) (Z := Z)).compr₂
        (map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)) =
      ((cup (Y := W) (Z := V)).compl₂ (map φ Z V hZ)).comp (map φ Y W hY) := by
    apply cupPairing_hom_ext
    intro X Q
    change map φ (Y ⊓ Z) (W ⊓ V) (supportPullback_inf_le φ hY hZ)
        (cup (mk Y X) (mk Z Q)) = cup (map φ Y W hY (mk Y X)) (map φ Z V hZ (mk Z Q))
    simp only [cup_mk_mk, tensorClass, map_mk]
    exact mk_iso _ (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      ((homotopyQuot S).mapIso (cochainTensorBaseChangeIso φ
        (supportedPerfectRepresentative X) (supportedPerfectRepresentative Q)))))
  exact DFunLike.congr_fun (DFunLike.congr_fun he x) y
end K0WithSupport
end SerrePositivity

end TensorBaseChangePart

section TensorAcyclicPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

lemma cochainAcyclic_iff_support_bot (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    P.Acyclic ↔ HasHomologySupportOn (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R)) P := by
  rw [hasHomologySupportOn_bot_iff]
  exact forall_congr' (fun i => HomologicalComplex.exactAt_iff_isZero_homology P i)

/-- A strictly perfect right factor preserves arbitrary quasi-isomorphisms. -/
lemma cochainTensor_quasiIso_left_of_perfect
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (hq : strictlyPerfectComplex R Q)
    (f : P ⟶ P') [QuasiIso f] : QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  obtain ⟨a, b, ha, hb⟩ := hq.1
  apply cochainTensor_quasiIso_left_of_boundedFlat Q a b
    (fun i hi => Q.isZero_of_isStrictlyGE a i hi)
    (fun i hi => Q.isZero_of_isStrictlyLE b i hi)
  intro i
  have := (hq.2 i).2
  infer_instance
end SerrePositivity

end TensorAcyclicPart
