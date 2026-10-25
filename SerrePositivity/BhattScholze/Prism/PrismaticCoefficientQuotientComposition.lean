module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient

/-! # prism係数の二段商と実導来基底変更

既存の実導来関手を、A→A/(a)→A/(a,d)の標準因数分解に沿って比較する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A)
local notation "I₀" => Ideal.span (Set.singleton a)
local notation "J₀" => Ideal.span (Set.insert a (Set.singleton d))
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "r₀" => Ideal.Quotient.mk J₀

/-- prism係数の二段商における標準の第2商射。 -/
def prismaticCoefficientPrincipalQuotientMap : A ⧸ I₀ →+* A ⧸ J₀ :=
  Ideal.quotientMap J₀ (RingHom.id A) (by
    intro x hx
    change x ∈ J₀
    exact (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) hx)

local notation "s₀" => prismaticCoefficientPrincipalQuotientMap a d

/-- 二段商の合成は、実際の(a,d)商射そのもの。 -/
theorem prismaticCoefficientPrincipalQuotientMap_comp : (s₀).comp q₀ = r₀ := by
  apply RingHom.ext
  intro x
  rfl

/-- 通常係数拡大の二段商比較はMathlibの標準合成比較から得る。 -/
def prismaticCoefficientScalarExtensionCompositionIso :
    ModuleCat.extendScalars r₀ ≅ ModuleCat.extendScalars q₀ ⋙ ModuleCat.extendScalars s₀ :=
  eqToIso (congrArg ModuleCat.extendScalars
      (prismaticCoefficientPrincipalQuotientMap_comp a d).symm) ≪≫
    ModuleCat.extendScalarsComp q₀ s₀

/-- 二段商の比較は複体上でも自然に成立する。 -/
def prismaticCoefficientCochainCompositionIso :
    (ModuleCat.extendScalars r₀).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars q₀).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.extendScalars s₀).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (prismaticCoefficientScalarExtensionCompositionIso a d).symm (.up ℤ)).symm

/-- 実(a,d)基底変更は、標準二段商に沿う二つの実導来基底変更と同型。 -/
def prismaticCoefficientDerivedQuotientCompositionIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) :
    (boundedAboveDerivedBaseChange r₀).obj X ≅
      (boundedAboveDerivedBaseChange s₀).obj ((boundedAboveDerivedBaseChange q₀).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso ((prismaticCoefficientCochainCompositionIso a d).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      (boundedAboveDerivedBaseChangeModelIso s₀ ((boundedAboveDerivedBaseChange q₀).obj X)
        (boundedAboveDerivedBaseChangeModel q₀ X)).symm)

/-- 二段商の実導来比較は、全ての実導来射に自然。 -/
theorem prismaticCoefficientDerivedQuotientCompositionIso_naturality
    {X Y : DerivedCategory.Minus (ModuleCat.{u} A)} (f : X ⟶ Y) :
    (boundedAboveDerivedBaseChange r₀).map f ≫
        (prismaticCoefficientDerivedQuotientCompositionIso a d Y).hom =
      (prismaticCoefficientDerivedQuotientCompositionIso a d X).hom ≫
        (boundedAboveDerivedBaseChange s₀).map ((boundedAboveDerivedBaseChange q₀).map f) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  let S := boundedAboveDerivedBaseChangeModel q₀ X
  let T := boundedAboveDerivedBaseChangeModel q₀ Y
  let k := ((ModuleCat.extendScalars q₀).mapHomologicalComplex (.up ℤ)).map h
  have hk : DerivedCategory.Q.map k ≫ T.iso.hom =
      S.iso.hom ≫ ((boundedAboveDerivedBaseChange q₀).map f).hom := by
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  have hr := boundedAboveLeftDerivedModelIso_naturality (ModuleCat.extendScalars s₀)
    S T ((boundedAboveDerivedBaseChange q₀).map f) k hk
  have hc := congrArg (fun g => DerivedCategory.Q.map g)
    ((prismaticCoefficientCochainCompositionIso a d).hom.naturality h)
  simp only [CategoryTheory.Functor.map_comp] at hc
  apply InducedCategory.hom_ext
  apply (cancel_mono (boundedAboveDerivedBaseChangeModelIso s₀
    ((boundedAboveDerivedBaseChange q₀).obj Y) T).hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    prismaticCoefficientDerivedQuotientCompositionIso, ObjectProperty.isoMk,
    ObjectProperty.homMk_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id]
  change DerivedCategory.Q.map
      (((ModuleCat.extendScalars r₀).mapHomologicalComplex (.up ℤ)).map h) ≫
        DerivedCategory.Q.map ((prismaticCoefficientCochainCompositionIso a d).hom.app Q.complex) =
    DerivedCategory.Q.map ((prismaticCoefficientCochainCompositionIso a d).hom.app P.complex) ≫
      (boundedAboveLeftDerivedModelIso (ModuleCat.extendScalars s₀) _ S).inv ≫
        ((boundedAboveLeftDerived (ModuleCat.extendScalars s₀)).map
          ((boundedAboveDerivedBaseChange q₀).map f)).hom ≫
        (boundedAboveLeftDerivedModelIso (ModuleCat.extendScalars s₀) _ T).hom
  rw [hr, Iso.inv_hom_id_assoc]
  exact hc

/-- 二段商比較の、実導来関手の自然同型としての公開入口。 -/
def prismaticCoefficientDerivedQuotientCompositionNatIso :
    boundedAboveDerivedBaseChange r₀ ≅
      boundedAboveDerivedBaseChange q₀ ⋙ boundedAboveDerivedBaseChange s₀ :=
  NatIso.ofComponents (prismaticCoefficientDerivedQuotientCompositionIso a d)
    (fun f => prismaticCoefficientDerivedQuotientCompositionIso_naturality a d f)

end SerrePositivity.BhattScholze
