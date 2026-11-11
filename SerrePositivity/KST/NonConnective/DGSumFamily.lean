module

public import SerrePositivity.KST.NonConnective.DGCountableSum

/-!
概要：実 dg 加群に値を持つ dg 関手族の、全次数での直和。
方針：実加群の全 Hom 余積普遍性を、族の各元の chain map に適用する。
規約：全次数の単位・合成保存を証明し、通常の関手族の直和とは区別する。
使われ方：id と可算直和関手の dg 直和と swindle の全 Hom 自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {C : Type w} [DGCategory R C] {J : Type t} [Small.{u} J]
  (F : J → DGFunctor R C (ModuleCategory R D))

/-- 元の dg 関手族の対象ごとの実直和。 -/
abbrev dgSumFamilyObj (X : C) : ModuleCategory R D := ∐ (fun j ↦ (F j).obj X)

/-- 元の全 Hom 作用を各成分への後合成から延長した実 chain map。 -/
def dgSumFamilyHom (X Y : C) :
    (X ⟶[Complex R] Y) ⟶ (dgSumFamilyObj R D F X ⟶[Complex R] dgSumFamilyObj R D F Y) :=
  moduleCoproductHomLift R D (fun j ↦ (F j).obj X) (dgSumFamilyObj R D F Y)
    (Fan.mk (X ⟶[Complex R] Y) (fun j ↦
      (F j).map X Y ≫ eHomWhiskerLeft (Complex R) ((F j).obj X)
        (Sigma.ι (fun j ↦ (F j).obj Y) j)))

/-- 各注入への制限は、元の同じ dg 関手の全 Hom 作用。 -/
@[reassoc] lemma dgSumFamilyHom_injection (X Y : C) (j : J) :
    dgSumFamilyHom R D F X Y ≫ eHomWhiskerRight (Complex R)
      (Sigma.ι (fun j ↦ (F j).obj X) j) (dgSumFamilyObj R D F Y) =
      (F j).map X Y ≫ eHomWhiskerLeft (Complex R) ((F j).obj X)
        (Sigma.ι (fun j ↦ (F j).obj Y) j) := moduleCoproductHomLift_π R D _ _ _ j

/-- 直和の全 Hom 作用は単位を保存する。 -/
lemma dgSumFamilyHom_id (X : C) :
    eId (Complex R) X ≫ dgSumFamilyHom R D F X X = eId (Complex R) (dgSumFamilyObj R D F X) := by
  apply (moduleCoproductHomIsLimit R D (fun j ↦ (F j).obj X) (dgSumFamilyObj R D F X)).hom_ext
  intro j
  change (eId (Complex R) X ≫ dgSumFamilyHom R D F X X) ≫
    eHomWhiskerRight (Complex R) (Sigma.ι (fun j ↦ (F j).obj X) j.as) _ =
      eId (Complex R) (dgSumFamilyObj R D F X) ≫
        eHomWhiskerRight (Complex R) (Sigma.ι (fun j ↦ (F j).obj X) j.as) _
  rw [Category.assoc, dgSumFamilyHom_injection, ← Category.assoc, (F j.as).map_id]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_postcompose (Complex R) (ModuleCategory R D) _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_precompose (Complex R) (ModuleCategory R D) _).symm

/-- 直和の全 Hom 作用は豊穣合成を保存する。 -/
lemma dgSumFamilyHom_comp (X Y Z : C) :
    eComp (Complex R) X Y Z ≫ dgSumFamilyHom R D F X Z =
      (dgSumFamilyHom R D F X Y ⊗ₘ dgSumFamilyHom R D F Y Z) ≫
        eComp (Complex R) (dgSumFamilyObj R D F X) (dgSumFamilyObj R D F Y)
          (dgSumFamilyObj R D F Z) := by
  apply (moduleCoproductHomIsLimit R D (fun j ↦ (F j).obj X) (dgSumFamilyObj R D F Z)).hom_ext
  intro j
  change (eComp (Complex R) X Y Z ≫ dgSumFamilyHom R D F X Z) ≫
    eHomWhiskerRight (Complex R) (Sigma.ι (fun j ↦ (F j).obj X) j.as) _ =
      ((dgSumFamilyHom R D F X Y ⊗ₘ dgSumFamilyHom R D F Y Z) ≫
        eComp (Complex R) (dgSumFamilyObj R D F X) (dgSumFamilyObj R D F Y)
          (dgSumFamilyObj R D F Z)) ≫
        eHomWhiskerRight (Complex R) (Sigma.ι (fun j ↦ (F j).obj X) j.as) _
  rw [Category.assoc, dgSumFamilyHom_injection, ← Category.assoc, (F j.as).map_comp]
  rw [Category.assoc, eComp_eHomWhiskerLeft]
  symm
  rw [Category.assoc, eComp_eHomWhiskerRight, tensorHom_def', Category.assoc,
    ← comp_whiskerRight_assoc, dgSumFamilyHom_injection, comp_whiskerRight_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_middle, whisker_exchange_assoc,
    ← whiskerLeft_comp_assoc, dgSumFamilyHom_injection]
  simp only [whiskerLeft_comp, Category.assoc, tensorHom_def', whisker_exchange_assoc]

/-- 同じ実 dg 関手族の直和は、厳密 dg 関手。 -/
def dgSumFamilyFunctor : DGFunctor R C (ModuleCategory R D) where
  obj := dgSumFamilyObj R D F
  map := dgSumFamilyHom R D F
  map_id := dgSumFamilyHom_id R D F
  map_comp := dgSumFamilyHom_comp R D F

end SerrePositivity.KST.NonConnective
