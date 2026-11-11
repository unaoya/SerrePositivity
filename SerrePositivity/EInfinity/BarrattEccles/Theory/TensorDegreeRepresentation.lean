module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.RepresentationTheory.Coinvariants

/-!
# 群作用を保つテンソルの次数分解

## 概要
Berger–Moerdijk §1 の Schur 表示を、arity とテンソルの双次数ごとに分解する。

## 方針
複体の群作用を次数で評価し、双次数の包含が作る表現の余積を使う。

## 規約
作用は左作用で、余不変は対角作用について取る。

## 使われ方
Barratt–Eccles のセル代数の次数付き基底。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits MonoidalCategory HomologicalComplex

variable {A G : Type u} [CommRing A] [Group G]
  {K L : CochainComplex (ModuleCat.{u} A) ℤ}

/-- A complex action evaluated in a specified cochain degree. -/
def complexDegreeRepresentation (ρ : G →* End K) (i : ℤ) :
    Representation A G (K.X i) :=
  (ModuleCat.endRingEquiv (K.X i)).toMonoidHom.comp
    (((HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).mapEnd (X := K)).comp ρ)

/-- The diagonal action on a tensor product of complexes. -/
def tensorComplexAction (ρ : G →* End K) (σ : G →* End L) : G →* End (K ⊗ L) where
  toFun g := .of ((ρ g).asHom ⊗ₘ (σ g).asHom)
  map_one' := by
    apply End.ext
    simp
  map_mul' g h := by
    apply End.ext
    simp only [map_mul, End.mul_asHom, tensorHom_comp_tensorHom]

/-- The representation in one bidegree of a tensor complex. -/
def tensorDegreeRepresentationSummand (ρ : G →* End K) (σ : G →* End L) (i : ℤ)
    (a : {a : ℤ × ℤ // a.1 + a.2 = i}) : Rep.{u} A G :=
  Rep.of (complexDegreeRepresentation ρ a.1.1) ⊗
    Rep.of (complexDegreeRepresentation σ a.1.2)

/-- The inclusion of one bidegree respects the diagonal action. -/
def tensorDegreeRepresentationLeg (ρ : G →* End K) (σ : G →* End L) (i : ℤ)
    (a : {a : ℤ × ℤ // a.1 + a.2 = i}) :
    tensorDegreeRepresentationSummand ρ σ i a ⟶
      Rep.of (complexDegreeRepresentation (tensorComplexAction ρ σ) i) :=
  Rep.ofHom ⟨(ιTensorObj K L a.1.1 a.1.2 i a.2).hom, fun g => by
    have h := ιTensorObj_cochainTensorMap (ρ g).asHom (σ g).asHom a.1.1 a.1.2 i a.2
    exact congrArg ModuleCat.Hom.hom h.symm⟩

/-- The bidegree cocone in the category of representations. -/
def tensorDegreeRepresentationCofan (ρ : G →* End K) (σ : G →* End L) (i : ℤ) :
    Cofan (tensorDegreeRepresentationSummand ρ σ i) :=
  Cofan.mk (Rep.of (complexDegreeRepresentation (tensorComplexAction ρ σ) i))
    (tensorDegreeRepresentationLeg ρ σ i)

/-- The bidegree cocone is colimiting, including its specified inclusion maps. -/
def tensorDegreeRepresentationIsColimit (ρ : G →* End K) (σ : G →* End L) (i : ℤ) :
    IsColimit (tensorDegreeRepresentationCofan ρ σ i) := by
  let U := forget₂ (Rep.{u} A G) (ModuleCat.{u} A)
  letI : ReflectsColimitsOfSize.{u, u} U := inferInstance
  letI : ReflectsColimitsOfSize.{0, 0} U :=
    reflectsSmallestColimits_of_reflectsColimits U
  apply isColimitOfIsColimitCofanMkObj U (tensorDegreeRepresentationSummand ρ σ i)
    (tensorDegreeRepresentationLeg ρ σ i)
  let V (a : {a : ℤ × ℤ // a.1 + a.2 = i}) := K.X a.1.1 ⊗ L.X a.1.2
  refine (colimit.isColimit (Discrete.functor V)).ofIsoColimit ?_
  refine Cofan.ext (Iso.refl _) ?_
  intro a
  rfl

/-- The coinvariants of a tensor degree are the coproduct of the bidegree coinvariants. -/
def tensorDegreeCoinvariantsIso (ρ : G →* End K) (σ : G →* End L) (i : ℤ) :
    ModuleCat.of A (complexDegreeRepresentation (tensorComplexAction ρ σ) i).Coinvariants ≅
      ∐ (fun a => ModuleCat.of A
        (tensorDegreeRepresentationSummand ρ σ i a).ρ.Coinvariants) := by
  let F := Rep.coinvariantsFunctor A G
  let h := isColimitCofanMkObjOfIsColimit F (tensorDegreeRepresentationSummand ρ σ i)
    (tensorDegreeRepresentationLeg ρ σ i) (tensorDegreeRepresentationIsColimit ρ σ i)
  exact h.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor _))

end SerrePositivity.EInfinity
