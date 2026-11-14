module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.CommutativeAlgebra.MappedPrincipalQuotient
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierRepresentatives
public import SerrePositivity.HomologicalAlgebra.DerivedTensorCartierProducts

/-! # 反復した (p, d) 完備テンソル積の H⁰ と Cartier 商

## 概要

反復した (p, d) 完備化の代数の `H⁰` を二座標の実際の完備化と比べ、反復完備テンソル積の `H⁰` が両方の座標について完備であることを示す。正則な主イデアルの基底変更の後の反復完備テンソル積を、二つの剰余因子の Tor の入力を保ったまま比較し、剰余因子の代数写像から反復 Cartier 商への写像、完備化の単位と代表の類の上の線形な Cartier 比較、完備な純テンソルの類の上の比較を与える。
BS 著者版 Lemma 3.5 のイデアル比較に関わる、反復完備テンソルの Cartier 商を計算する。

## 方針

外側の完備化の単位と元の内側の完備化の単位で比較を決める。

## 規約

名前空間 `SerrePositivity.DerivedCompletion` と宣言名は変えない。旧 `HomologicalAlgebra/DerivedCompletion/Iterated*` の 6 本（BS の完全 prism のテンソル積専用なので、2a で BS の下へ移した。refactor-plan §3.8 の 4）。

## 使われ方

`Prism/Tensor/PerfectPrismTensor`。
-/

@[expose] public noncomputable section

universe u

section IteratedAlgebraH0ComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (d : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) [A.X.obj.IsLE 0]
set_option quotPrecheck false in
local notation "AP" => (boundedAboveCompletionCommMonFunctor R (p : R)).obj A
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AP).X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R d).obj AP).X.obj
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R d AP)
/-- Actual iterated p,d completion has the actual F3 H⁰ algebra of the first H⁰. -/
def iteratedAlgebraCompletionH0PDAlgEquiv :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := completionH0ScalarAlgebra R d AP
    letI := pdCompletionCommRing B p (algebraMap R B d)
    letI := pdCompletionAlgebra B p (algebraMap R B d)
    C ≃ₐ[B] PDCompletionH0 B p (algebraMap R B d) := by
  letI := derivedH0CommRing AP
  letI := derivedH0Algebra AP
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  letI := completionH0ScalarAlgebra R d AP
  letI := pdCompletionCommRing B p (algebraMap R B d)
  letI := pdCompletionAlgebra B p (algebraMap R B d)
  let hle : (AP).X.obj.IsLE 0 :=
    boundedAboveDerivedCompletionFunctor_isLE R (p : R) A.X 0 inferInstance
  have hB : IsModuleComplete R (p : R) B :=
    derivedComplexCompletionFunctor_homology_isModuleComplete R (p : R) A.X.obj 0
  have aux (c : B) (hc : algebraMap R B (p : R) = c) :
      letI := pairCompletionCommRing B c (algebraMap R B d)
      letI := pairCompletionAlgebra B c (algebraMap R B d)
      C ≃ₐ[B] PairCompletionH0 B c (algebraMap R B d) := by
    subst c
    exact completionH0PairAlgEquivOfCompleteFirst R d AP (p : R) hB
  exact aux (p : B) (map_natCast (algebraMap R B) p)

variable (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "ATP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "BT" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ATP).X.obj
/-- The original completed derived tensor followed by d-completion, as a coefficient algebra. -/
def iteratedCompletedTensorH0PDAlgEquiv :
    letI := derivedH0CommRing ATP
    letI := derivedH0Algebra ATP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := completionH0ScalarAlgebra R d ATP
    letI := pdCompletionCommRing BT p (algebraMap R BT d)
    letI := pdCompletionAlgebra BT p (algebraMap R BT d)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R d).obj ATP).X.obj ≃ₐ[BT]
      PDCompletionH0 BT p (algebraMap R BT d) := by
  letI := derivedH0CommRing ATP
  letI := derivedH0Algebra ATP
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  letI := completionH0ScalarAlgebra R d ATP
  letI := pdCompletionCommRing BT p (algebraMap R BT d)
  letI := pdCompletionAlgebra BT p (algebraMap R BT d)
  let hle : (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R S)).obj
      (ModuleCat.of R T)).IsLE 0
    infer_instance
  exact iteratedAlgebraCompletionH0PDAlgEquiv R p d
    (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- In particular the standard image of the original d is retained by this comparison. -/
lemma iteratedCompletedTensorH0PDAlgEquiv_unit (x : BT) :
    letI := derivedH0CommRing ATP
    letI := derivedH0Algebra ATP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := completionH0ScalarAlgebra R d ATP
    letI := pdCompletionCommRing BT p (algebraMap R BT d)
    letI := pdCompletionAlgebra BT p (algebraMap R BT d)
    iteratedCompletedTensorH0PDAlgEquiv R p d S T
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R d ATP) x) =
        pdCompletionUnit BT p (algebraMap R BT d) x := by
  let := derivedH0CommRing ATP
  let := derivedH0Algebra ATP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := completionH0ScalarAlgebra R d ATP
  let := pdCompletionCommRing BT p (algebraMap R BT d)
  let := pdCompletionAlgebra BT p (algebraMap R BT d)
  exact (iteratedCompletedTensorH0PDAlgEquiv R p d S T).commutes x

/-- The original base scalar, in particular the original d generator, is preserved. -/
lemma iteratedCompletedTensorH0PDAlgEquiv_algebraMap (r : R) :
    letI := derivedH0CommRing ATP
    letI := derivedH0Algebra ATP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := completionH0ScalarAlgebra R d ATP
    letI := pdCompletionCommRing BT p (algebraMap R BT d)
    letI := pdCompletionAlgebra BT p (algebraMap R BT d)
    iteratedCompletedTensorH0PDAlgEquiv R p d S T
      (algebraMap R ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveCompletionCommMonFunctor R d).obj ATP).X.obj) r) =
      pdCompletionUnit BT p (algebraMap R BT d) (algebraMap R BT r) := by
  let := derivedH0CommRing ATP
  let := derivedH0Algebra ATP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := completionH0ScalarAlgebra R d ATP
  let := pdCompletionCommRing BT p (algebraMap R BT d)
  let := pdCompletionAlgebra BT p (algebraMap R BT d)
  have h := iteratedCompletedTensorH0PDAlgEquiv_unit R p d S T (algebraMap R BT r)
  rw [AlgHom.commutes] at h
  exact h

end SerrePositivity.DerivedCompletion

end IteratedAlgebraH0ComparisonPart

section IteratedTensorH0CompletePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (d : R)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AP).X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R d).obj AP).X.obj
/-- The original second completed H⁰ retains p-completeness as a ring. -/
lemma iteratedCompletedTensorH0_self_complete_p :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    IsModuleComplete C (p : C) (ModuleCat.of C C) := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := completionH0ScalarAlgebra R d AP
  let := completionH0ScalarTower R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  let P := PDCompletionH0 B p (algebraMap R B d)
  let e := iteratedCompletedTensorH0PDAlgEquiv R p d S T
  have hc : IsModuleComplete B (p : B) (ModuleCat.of B C) :=
    isModuleComplete_of_linearEquiv B (p : B) (ModuleCat.of B P) (ModuleCat.of B C)
      e.symm.toLinearEquiv (pairCompletionH0_isModuleComplete_first B (p : B) (algebraMap R B d))
  have ht := (isModuleComplete_algebraMap_iff B C (p : B) C).mpr hc
  simpa only [map_natCast] using ht

/-- The original image of d is a complete coordinate of the second actual H⁰ ring. -/
lemma iteratedCompletedTensorH0_self_complete_d :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    IsModuleComplete C (algebraMap R C d) (ModuleCat.of C C) := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := completionH0ScalarAlgebra R d AP
  let := completionH0ScalarTower R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  let P := PDCompletionH0 B p (algebraMap R B d)
  let e := iteratedCompletedTensorH0PDAlgEquiv R p d S T
  have hc : IsModuleComplete B (algebraMap R B d) (ModuleCat.of B C) :=
    isModuleComplete_of_linearEquiv B (algebraMap R B d) (ModuleCat.of B P) (ModuleCat.of B C)
      e.symm.toLinearEquiv
      (pairCompletionH0_isModuleComplete_second B (p : B) (algebraMap R B d))
  have ht := (isModuleComplete_algebraMap_iff B C (algebraMap R B d) C).mpr hc
  simpa only [← IsScalarTower.algebraMap_apply R B C d] using ht

end SerrePositivity.DerivedCompletion

end IteratedTensorH0CompletePart

section IteratedTensorQuotientComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (a b : R) (hb : IsSMulRegular R b)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {b})
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {b}
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {b})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {b})
set_option quotPrecheck false in
local notation "X" => (boundedAboveDerivedTensorAlgebra (R := R) S T).X
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R b).obj AP

include hb in
/-- The quotient of the outer completion unit is the original actual isomorphism. -/
lemma iteratedTensor_outerQuotientUnit_isIso :
    IsIso (((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) := by
  have aux (c : R) (hc : b ^ 1 = c) :
      IsIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {c}))).map
        ((boundedAboveDerivedCompletionUnit R b).app (AP).X)) := by
    subst c
    exact boundedAboveDerivedCompletion_quotient_unit_isIso R b hb 1 (AP).X
  have hi := aux b (pow_one b)
  change IsIso (DerivedCategory.Minus.ι.map
    ((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R b).app (AP).X)))
  infer_instance

/-- Quotient the original a,b-completed tensor, or a-complete the actual quotient tensor. -/
def iteratedCompletedTensorQuotientIso
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    ((boundedAboveDerivedBaseChange (q)).obj (AD).X).obj ≅
      (derivedComplexCompletionFunctor Q ((q) a)).obj
        (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj := by
  have := iteratedTensor_outerQuotientUnit_isIso R a b hb S T
  exact (asIso (((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom)).symm ≪≫
    (completionQuotientBaseChangeIso R a b hb X).symm ≪≫
    (derivedComplexCompletionFunctor Q ((q) a)).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT))

/-- The outer standard unit is removed by the comparison without replacing that unit. -/
lemma iteratedCompletedTensorQuotientIso_outer_unit
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).hom =
      (completionQuotientBaseChangeIso R a b hb X).inv ≫
        (derivedComplexCompletionFunctor Q ((q) a)).map
          (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom := by
  have := iteratedTensor_outerQuotientUnit_isIso R a b hb S T
  simp only [iteratedCompletedTensorQuotientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  rfl

/-- Both original completion units are sent to the standard completion unit of the quotient tensor. -/
lemma iteratedCompletedTensorQuotientIso_units
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X ≫
          (boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).hom =
      (derivedComplexCompletionUnit Q ((q) a)).app
          ((boundedAboveDerivedBaseChange (q)).obj X).obj ≫
        (derivedComplexCompletionFunctor Q ((q) a)).map
          (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom := by
  rw [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    iteratedCompletedTensorQuotientIso_outer_unit, ← Category.assoc]
  have hu := completionQuotientBaseChangeComparison_unit R a b hb X
  have hi : (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom) ≫
        (completionQuotientBaseChangeIso R a b hb X).inv =
      (derivedComplexCompletionUnit Q ((q) a)).app
        ((boundedAboveDerivedBaseChange (q)).obj X).obj := by
    rw [← hu]
    change ((derivedComplexCompletionUnit Q ((q) a)).app _ ≫
      (completionQuotientBaseChangeIso R a b hb X).hom) ≫
        (completionQuotientBaseChangeIso R a b hb X).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hi]

/-- The inverse quotient comparison sends the original residue completion unit to both units. -/
lemma iteratedCompletedTensorQuotientIso_inv_units
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom ≫
        (derivedComplexCompletionUnit Q ((q) a)).app
          (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).inv =
      (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X ≫
          (boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) := by
  have hu := iteratedCompletedTensorQuotientIso_units R a b hb S T hS hT
  have hn := (derivedComplexCompletionUnit Q ((q) a)).naturality
    (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom
  simp only [Functor.id_map] at hn
  have hn' :
      (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom ≫
          (derivedComplexCompletionUnit Q ((q) a)).app
            (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj =
        (derivedComplexCompletionUnit Q ((q) a)).app
            ((boundedAboveDerivedBaseChange (q)).obj X).obj ≫
          (derivedComplexCompletionFunctor Q ((q) a)).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom := hn
  rw [← hn'] at hu
  calc
    _ = ((((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X ≫
          (boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).hom) ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).inv := by
      rw [hu, Category.assoc]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Separate regularity of the two factors supplies the two ordinary-residue Tor inputs. -/
def regularIteratedCompletedTensorQuotientIso
    (hs : IsSMulRegular S b) (ht : IsSMulRegular T b) :
    ((boundedAboveDerivedBaseChange (q)).obj (AD).X).obj ≅
      (derivedComplexCompletionFunctor Q ((q) a)).obj
        (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj :=
  iteratedCompletedTensorQuotientIso R a b hb S T
    (scalarExtensionTorVanishing_principal_of_regular b hb (ModuleCat.of R S) hs)
    (scalarExtensionTorVanishing_principal_of_regular b hb (ModuleCat.of R T) ht)

end SerrePositivity.DerivedCompletion

end IteratedTensorQuotientComparisonPart

section IteratedTensorCartierAlgebraPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX
/-- The original left factor map through both original completion units, on actual H⁰. -/
def iteratedTensorH0LeftAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    S →ₐ[R] C := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃ₐ[R] S :=
    derivedSingleH0AlgEquiv (R := R) S
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T ≫
    boundedAboveCompletionAlgebraUnit R d AP)).comp e.symm.toAlgHom

/-- The original left factor descends to the original ordinary residue ring over Q. -/
def iteratedTensorCartierLeftAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    SQ →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (principalAdicReductionAlgHom R d (iteratedTensorH0LeftAlgHom R a d S T)).comp
    (mappedPrincipalQuotientAlgEquiv R d S).toAlgHom

/-- The residue map retains the original representative and original factor action. -/
lemma iteratedTensorCartierLeftAlgHom_mk (x : S) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierLeftAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0LeftAlgHom R a d S T x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  change principalAdicReductionAlgHom R d (iteratedTensorH0LeftAlgHom R a d S T)
    (mappedPrincipalQuotientAlgEquiv R d S (Ideal.Quotient.mk _ x)) = _
  rw [mappedPrincipalQuotientAlgEquiv_mk, principalAdicReductionAlgHom_mk]

/-- The original right factor map through both original completion units, on actual H⁰. -/
def iteratedTensorH0RightAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    T →ₐ[R] C := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let e : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃ₐ[R] T :=
    derivedSingleH0AlgEquiv (R := R) T
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R a S T ≫
    boundedAboveCompletionAlgebraUnit R d AP)).comp e.symm.toAlgHom

/-- The original right factor descends to the original ordinary residue ring over Q. -/
def iteratedTensorCartierRightAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    TQ →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (principalAdicReductionAlgHom R d (iteratedTensorH0RightAlgHom R a d S T)).comp
    (mappedPrincipalQuotientAlgEquiv R d T).toAlgHom

/-- The residue map retains the original representative and original factor action. -/
lemma iteratedTensorCartierRightAlgHom_mk (x : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierRightAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) x) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0RightAlgHom R a d S T x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  change principalAdicReductionAlgHom R d (iteratedTensorH0RightAlgHom R a d S T)
    (mappedPrincipalQuotientAlgEquiv R d T (Ideal.Quotient.mk _ x)) = _
  rw [mappedPrincipalQuotientAlgEquiv_mk, principalAdicReductionAlgHom_mk]

/-- The ordinary residue tensor maps to the original Cartier quotient by its original factors. -/
def iteratedTensorCartierTensorAlgHom :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    SQ ⊗[Q] TQ →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact Algebra.TensorProduct.lift (iteratedTensorCartierLeftAlgHom R a d S T)
    (iteratedTensorCartierRightAlgHom R a d S T) (fun _ _ => Commute.all _ _)

/-- Pure tensors of original representatives have their original product Cartier image. -/
lemma iteratedTensorCartierTensorAlgHom_tmul (s : S) (t : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedTensorCartierTensorAlgHom R a d S T
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
          Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d}) (iteratedTensorH0LeftAlgHom R a d S T s) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0RightAlgHom R a d S T t) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  simp only [iteratedTensorCartierTensorAlgHom, Algebra.TensorProduct.lift_tmul]
  rw [iteratedTensorCartierLeftAlgHom_mk, iteratedTensorCartierRightAlgHom_mk]

set_option maxHeartbeats 800000 in
-- Elaborating this map compares the original R-H⁰ ring and both Q-derived H⁰ algebra instances.
/-- The canonical extension to actual completed residue-tensor H⁰, for the same Cartier quotient. -/
def iteratedTensorCartierCompletedAlgHom
    (hp :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj →ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
  letI := derivedH0CommRing RX
  letI := derivedH0Algebra RX
  letI := derivedH0CommRing RC
  letI := derivedH0Algebra RC
  let hle : (RX).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of Q SQ)).obj
      (ModuleCat.of Q TQ)).IsLE 0
    infer_instance
  exact completionH0AlgebraLift Q ((q) a) RX CQ hp
    ((iteratedTensorCartierTensorAlgHom R a d S T).comp
      (derivedTensorH0AlgEquiv (R := Q) SQ TQ).toAlgHom)

/-- This algebra extension retains the original actual residue-tensor completion unit. -/
lemma iteratedTensorCartierCompletedAlgHom_unit
    (hp :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ))
    (x : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RX).X.obj) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    iteratedTensorCartierCompletedAlgHom R a d S T hp
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q ((q) a) RX) x) =
      iteratedTensorCartierTensorAlgHom R a d S T
        (derivedTensorH0AlgEquiv (R := Q) SQ TQ x) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  let hle : (RX).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of Q SQ)).obj
      (ModuleCat.of Q TQ)).IsLE 0
    infer_instance
  have h := completionH0AlgebraLift_unit Q ((q) a) RX CQ hp
    ((iteratedTensorCartierTensorAlgHom R a d S T).comp
      (derivedTensorH0AlgEquiv (R := Q) SQ TQ).toAlgHom)
  exact congrArg (fun f => f x) h

end SerrePositivity.DerivedCompletion

end IteratedTensorCartierAlgebraPart

section IteratedTensorCartierLinearComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "X" => boundedAboveDerivedTensorAlgebra (R := R) S T
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX

/-- The original inverse tensor quotient comparison followed by the unchanged Cartier H⁰ map. -/
def iteratedCompletedTensorCartierH0Iso
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) :
    letI : (AD).X.obj.IsGE 0 := hpure.1
    letI : (AD).X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj ≅ ModuleCat.of Q CQ := by
  letI : (AD).X.obj.IsGE 0 := hpure.1
  letI : (AD).X.obj.IsLE 0 := hpure.2
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (iteratedCompletedTensorQuotientIso R a d hd S T hS hT).symm ≪≫
    pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC

/-- On the original unit, the linear comparison is the Cartier image of both original units. -/
lemma iteratedCompletedTensorCartierH0Iso_units
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (z : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange (q)).obj (X).X).obj) :
    letI : (AD).X.obj.IsGE 0 := hpure.1
    letI : (AD).X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom z)) =
      (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map
            ((boundedAboveDerivedCompletionUnit R a).app (X).X ≫
              (boundedAboveDerivedCompletionUnit R d).app (AP).X)).hom) z) := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  have hu := congrArg H0.map (iteratedCompletedTensorQuotientIso_inv_units
    R a d hd S T hS hT)
  rw [Functor.map_comp, Functor.map_comp] at hu
  have hz := congrArg (fun f => f z) hu
  simp only [ModuleCat.comp_apply] at hz
  change H0.map (iteratedCompletedTensorQuotientIso R a d hd S T hS hT).inv
      (H0.map ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
        (H0.map (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom z)) =
    H0.map (((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R a).app (X).X ≫
        (boundedAboveDerivedCompletionUnit R d).app (AP).X)).hom) z at hz
  exact congrArg (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom hz

/-- Original discrete source representatives keep their Cartier class under the comparison. -/
lemma iteratedCompletedTensorCartierH0Iso_single_map
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (U : Type u) [CommRing U] [Algebra R U] (hU : IsSMulRegular U d)
    (f : boundedAboveDerivedAlgebra (R := R) U ⟶ X) (s : U) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) U)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) U)
    let eU : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedAlgebra (R := R) U).X.obj ≃ₐ[R] U :=
      derivedSingleH0AlgEquiv (R := R) U
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
              (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom)
              ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R U)
                ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (derivedH0AlgMap (f ≫ boundedAboveCompletionAlgebraUnit R a X ≫
            boundedAboveCompletionAlgebraUnit R d AP)
          (eU.symm s)) := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) U)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) U)
  rw [iteratedCompletedTensorCartierH0Iso_units]
  have h := pureDerivedAlgebraCartierQuotientH0Iso_single_map R d U hd hU AD hC
    (f ≫ boundedAboveCompletionAlgebraUnit R a X ≫
      boundedAboveCompletionAlgebraUnit R d AP) s
  have hu : (f ≫ boundedAboveCompletionAlgebraUnit R a X ≫
        boundedAboveCompletionAlgebraUnit R d AP).hom.hom =
      f.hom.hom ≫ ((boundedAboveDerivedCompletionUnit R a).app (X).X ≫
        (boundedAboveDerivedCompletionUnit R d).app (AP).X) := by
    change f.hom.hom ≫ ((boundedAboveCompletionAlgebraUnit R a X).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R d AP).hom.hom) = _
    rw [boundedAboveCompletionAlgebraUnit_hom, boundedAboveCompletionAlgebraUnit_hom]
  rw [hu, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp] at h
  simp only [ModuleCat.comp_apply] at h
  exact h

/-- The linear comparison retains the original left factor's actual Cartier image. -/
lemma iteratedCompletedTensorCartierH0Iso_left
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hsrc : IsSMulRegular S d) (s : S) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
              (((boundedAboveDerivedBaseChange (q)).map
                (boundedAboveDerivedTensorAlgebraLeft (R := R) S T).hom.hom).hom)
              ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
                ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0LeftAlgHom R a d S T s) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  have h := iteratedCompletedTensorCartierH0Iso_single_map R a d hd S T hS hT hC hpure
    S hsrc (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) s
  simp only [iteratedTensorH0LeftAlgHom, boundedAboveCompletedTensorAlgebraLeft,
    Category.assoc, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at h ⊢
  exact h

/-- The linear comparison retains the original right factor's actual Cartier image. -/
lemma iteratedCompletedTensorCartierH0Iso_right
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hsrc : IsSMulRegular T d) (s : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
              (((boundedAboveDerivedBaseChange (q)).map
                (boundedAboveDerivedTensorAlgebraRight (R := R) S T).hom.hom).hom)
              ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R T)
                ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0RightAlgHom R a d S T s) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  have h := iteratedCompletedTensorCartierH0Iso_single_map R a d hd S T hS hT hC hpure
    T hsrc (boundedAboveDerivedTensorAlgebraRight (R := R) S T) s
  simp only [iteratedTensorH0RightAlgHom, boundedAboveCompletedTensorAlgebraRight,
    Category.assoc, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at h ⊢
  exact h

/-- This is exactly the homology of the original derived Cartier comparison. -/
lemma iteratedCompletedTensorCartierH0Iso_eq_derived
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) :
    letI : (AD).X.obj.IsGE 0 := hpure.1
    letI : (AD).X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure =
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
        ((iteratedCompletedTensorQuotientIso R a d hd S T hS hT).symm ≪≫
          DerivedCategory.Minus.ι.mapIso (pureDerivedAlgebraCartierQuotientIso R d hd AD hC)) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).app _ := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  apply Iso.ext
  simp only [iteratedCompletedTensorCartierH0Iso, pureDerivedAlgebraCartierQuotientH0Iso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

end SerrePositivity.DerivedCompletion

end IteratedTensorCartierLinearComparisonPart

section IteratedTensorCartierProductsPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "X" => boundedAboveDerivedTensorAlgebra (R := R) S T
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX

/-- The original linear comparison sends completed pure tensors to their original factor product. -/
lemma iteratedCompletedTensorCartierH0Iso_unit_tmul
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) (s : S) (t : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    let eQ : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RX).X.obj ≃ₐ[Q]
        SQ ⊗[Q] TQ := derivedTensorH0AlgEquiv (R := Q) SQ TQ
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          (eQ.symm
            (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
              Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0LeftAlgHom R a d S T s) *
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
          (iteratedTensorH0RightAlgHom R a d S T t) := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let eQ : H0.obj (RX).X.obj ≃ₐ[Q] SQ ⊗[Q] TQ :=
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
  let z := (derivedTensorQuotientBaseChangeH0Iso (Ideal.span {d}) S T hS hT).inv
    ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] (s ⊗ₜ[R] t))
  have hclass : eQ.symm
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
          Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t) =
      H0.map (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom z := by
    apply eQ.injective
    rw [eQ.apply_symm_apply]
    exact (derivedTensorQuotientAlgebraIso_homology_tmul (Ideal.span {d}) S T hS hT s t).symm
  let u : X ⟶ AD := boundedAboveCompletionAlgebraUnit R a X ≫
    boundedAboveCompletionAlgebraUnit R d AP
  let u0 : (X).X ⟶ (AD).X := u.hom.hom
  have hu : u0 = (boundedAboveDerivedCompletionUnit R a).app (X).X ≫
      (boundedAboveDerivedCompletionUnit R d).app (AP).X := by
    change (boundedAboveCompletionAlgebraUnit R a X).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R d AP).hom.hom = _
    rw [boundedAboveCompletionAlgebraUnit_hom, boundedAboveCompletionAlgebraUnit_hom]
  have hU := congrArg (fun f => (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom
    (H0.map (((boundedAboveDerivedBaseChange (q)).map f).hom) z)) hu
  have h2 := pureDerivedAlgebraCartierQuotientH0Iso_tensor_representative_mul
    R d hd S T AD hS hT hC u s t
  have hright := hU.symm.trans h2
  simp only [u, iteratedTensorH0LeftAlgHom, iteratedTensorH0RightAlgHom,
    boundedAboveCompletedTensorAlgebraLeft, boundedAboveCompletedTensorAlgebraRight,
    Category.assoc, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at hright ⊢
  have h1 := iteratedCompletedTensorCartierH0Iso_units R a d hd S T hS hT hC hpure z
  have hpre := congrArg (fun v =>
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
      (H0.map ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj) v)) hclass
  exact hpre.trans (h1.trans hright)

/-- The original linear Cartier iso is the standard algebra extension on the same H⁰ rings. -/
lemma iteratedCompletedTensorCartierH0Iso_eq_algHom
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RX
    letI := derivedH0Algebra RX
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom.hom =
      (iteratedTensorCartierCompletedAlgHom R a d S T hp).toLinearMap := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RX
  let := derivedH0Algebra RX
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let eQ : H0.obj (RX).X.obj ≃ₐ[Q] SQ ⊗[Q] TQ :=
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
  let l : H0.obj (RC).X.obj →ₗ[Q] CQ :=
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom.hom
  let k : H0.obj (RC).X.obj →ₐ[Q] CQ :=
    iteratedTensorCartierCompletedAlgHom R a d S T hp
  let j : H0.obj (RX).X.obj →ₐ[Q] H0.obj (RC).X.obj :=
    derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q ((q) a) RX)
  have hj (v : H0.obj (RX).X.obj) :
      j v = H0.map ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj) v :=
    completionH0AlgebraUnit_apply Q ((q) a) RX v
  have hext : (l.comp j.toLinearMap).comp eQ.symm.toLinearMap =
      (k.toLinearMap.comp j.toLinearMap).comp eQ.symm.toLinearMap := by
    apply TensorProduct.ext'
    intro sq tq
    refine Quotient.inductionOn' sq (fun s => ?_)
    refine Quotient.inductionOn' tq (fun t => ?_)
    let v := eQ.symm
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s ⊗ₜ[Q]
        Ideal.Quotient.mk (Ideal.map (algebraMap R T) (Ideal.span {d})) t)
    have hL : l (j v) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0LeftAlgHom R a d S T s) *
          Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0RightAlgHom R a d S T t) := by
      exact (congrArg l (hj v)).trans
        (iteratedCompletedTensorCartierH0Iso_unit_tmul R a d hd S T hS hT hC hpure s t)
    have hK : k (j v) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0LeftAlgHom R a d S T s) *
          Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
            (iteratedTensorH0RightAlgHom R a d S T t) := by
      change iteratedTensorCartierCompletedAlgHom R a d S T hp
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit Q ((q) a) RX) v) = _
      rw [iteratedTensorCartierCompletedAlgHom_unit]
      change iteratedTensorCartierTensorAlgHom R a d S T (eQ (eQ.symm _)) = _
      rw [eQ.apply_symm_apply, iteratedTensorCartierTensorAlgHom_tmul]
    exact hL.trans hK.symm
  let hle : (RX).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of Q SQ)).obj
      (ModuleCat.of Q TQ)).IsLE 0
    infer_instance
  change l = k.toLinearMap
  apply completionH0_linear_ext Q ((q) a) RX CQ hp
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hext (eQ x)
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.symm_apply_apply] at hx
  exact hx

/-- The standard completed residue tensor map is an algebra iso on the original H⁰ rings. -/
def iteratedTensorCartierCompletedAlgEquiv
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj ≃ₐ[Q] CQ := by
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
  letI := derivedH0CommRing RC
  letI := derivedH0Algebra RC
  let eL := iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure
  let k := iteratedTensorCartierCompletedAlgHom R a d S T hp
  have he := iteratedCompletedTensorCartierH0Iso_eq_algHom R a d hd S T hS hT hC hpure hp
  have hefun : (fun x => eL.hom x) = (fun x => k x) :=
    funext (fun x => LinearMap.congr_fun he x)
  have hb : Function.Bijective k :=
    (congrArg Function.Bijective hefun).mp eL.toLinearEquiv.bijective
  exact AlgEquiv.ofBijective k hb

/-- Its algebra map is precisely the original standard extension. -/
lemma iteratedTensorCartierCompletedAlgEquiv_toAlgHom
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).toAlgHom =
      iteratedTensorCartierCompletedAlgHom R a d S T hp := by
  rfl

/-- Its underlying linear equivalence is the original Cartier H⁰ comparison. -/
lemma iteratedTensorCartierCompletedAlgEquiv_toLinearEquiv
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hp :
      letI := derivedH0CommRing AD
      letI := derivedH0Algebra AD
      letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
      IsModuleComplete Q ((q) a) (ModuleCat.of Q CQ)) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI : Algebra Q CQ := principalAdicQuotientAlgebra d C
    letI := derivedH0CommRing RC
    letI := derivedH0Algebra RC
    (iteratedTensorCartierCompletedAlgEquiv R a d hd S T hS hT hC hpure hp).toLinearEquiv =
      (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).toLinearEquiv := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let : Algebra Q CQ := principalAdicQuotientAlgebra d C
  let := derivedH0CommRing RC
  let := derivedH0Algebra RC
  apply LinearEquiv.ext
  intro x
  exact (LinearMap.congr_fun
    (iteratedCompletedTensorCartierH0Iso_eq_algHom R a d hd S T hS hT hC hpure hp) x).symm

end SerrePositivity.DerivedCompletion

end IteratedTensorCartierProductsPart
