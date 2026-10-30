module

public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.HomologicalAlgebra.CochainTensorBoundedAbove
public import SerrePositivity.HomologicalAlgebra.CochainTensorBounds

/-! # 上に有界な導来圏のテンソル積

## 概要

上に有界な複体の射影分解によるテンソル積のモデル `tensorModel` と通常のテンソル複体への augmentation `tensorAugmentation` を作り、上に有界な導来圏上のテンソル積 `boundedAboveDerivedTensor` と、そのモデルとの同型 `boundedAboveDerivedTensorModelIso`（自然）を定める。

## 方針

K 射影的な分解とのテンソルが擬同型を保つこと（`cochainTensorMap_quasiIso_of_KProjective`）から、モデルの選び方によらないことを示す。

## 規約

結合子・単位・基底変換は BoundedAboveDerivedAssociator・BoundedAboveDerivedUnit・BoundedAboveDerivedBaseChange（BS が import するので別ファイルのまま）。

## 使われ方

BS の導来テンソル、HomologicalAlgebra の導来完備化。
-/

@[expose] public noncomputable section

universe u

section BoundedAboveTensorModelsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
namespace BoundedAboveProjectiveResolution

/-- Total tensor complex of two projective replacements. -/
abbrev tensorModel (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) := cochainTensor P.complex Q.complex

/-- Standard augmentation to the ordinary tensor complex. -/
def tensorAugmentation (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) : tensorModel P Q ⟶ cochainTensor K L :=
  cochainTensorMap P.π Q.π

end BoundedAboveProjectiveResolution
end SerrePositivity

end BoundedAboveTensorModelsPart

section BoundedAboveTensorFunctorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Tensoring quasi-isomorphisms between K-projective complexes preserves quasi-isomorphisms. -/
lemma cochainTensorMap_quasiIso_of_KProjective
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    [P.IsKProjective] [P'.IsKProjective] [Q.IsKProjective] [Q'.IsKProjective]
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (cochainTensorMap f g) := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  obtain ⟨e', he'⟩ := (CochainComplex.IsKProjective.quasiIso_iff g).mp inferInstance
  have h : (cochainTensorHomotopyEquiv e e').hom = cochainTensorMap f g := by
    simp [cochainTensorHomotopyEquiv, he, he']
  rw [← h]
  infer_instance

end SerrePositivity

end BoundedAboveTensorFunctorPart

section BoundedAboveDerivedTensorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Derived tensor is a bifunctor on Mathlib's bounded-above derived category.
Its values stay bounded above; arbitrary negative tails are allowed. -/
def boundedAboveDerivedTensor :
    (DerivedCategory.Minus (ModuleCat.{u} R) × DerivedCategory.Minus (ModuleCat.{u} R)) ⥤
      DerivedCategory.Minus (ModuleCat.{u} R) where
  obj X := by
    let P := boundedAboveDerivedChosenModel X.1
    let Q := boundedAboveDerivedChosenModel X.2
    have := cochainTensor_isStrictlyLE P.complex Q.complex P.bound Q.bound
    exact ⟨DerivedCategory.Q.obj (cochainTensor P.complex Q.complex),
      ⟨P.bound + Q.bound, inferInstance⟩⟩
  map {X Y} f := ObjectProperty.homMk (DerivedCategory.Q.map (cochainTensorMap
    ((boundedAboveDerivedChosenModel X.1).map (boundedAboveDerivedChosenModel Y.1) f.1.hom)
    ((boundedAboveDerivedChosenModel X.2).map (boundedAboveDerivedChosenModel Y.2) f.2.hom)))
  map_id X := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X.1
    let Q := boundedAboveDerivedChosenModel X.2
    change DerivedCategory.Q.map (cochainTensorMap (P.map P (𝟙 X.1.obj))
      (Q.map Q (𝟙 X.2.obj))) = _
    have h := (cochainTensorHomotopyLeft P.mapIdHomotopy (Q.map Q (𝟙 X.2.obj))).trans
      (cochainTensorHomotopyRight (𝟙 P.complex) Q.mapIdHomotopy)
    rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R) h,
      cochainTensorMap_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X.1
    let P' := boundedAboveDerivedChosenModel Y.1
    let P'' := boundedAboveDerivedChosenModel Z.1
    let Q := boundedAboveDerivedChosenModel X.2
    let Q' := boundedAboveDerivedChosenModel Y.2
    let Q'' := boundedAboveDerivedChosenModel Z.2
    change DerivedCategory.Q.map (cochainTensorMap
      (P.map P'' (f.1.hom ≫ g.1.hom)) (Q.map Q'' (f.2.hom ≫ g.2.hom))) =
      DerivedCategory.Q.map (cochainTensorMap (P.map P' f.1.hom) (Q.map Q' f.2.hom)) ≫
        DerivedCategory.Q.map (cochainTensorMap (P'.map P'' g.1.hom) (Q'.map Q'' g.2.hom))
    rw [← CategoryTheory.Functor.map_comp, cochainTensorMap_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
      ((cochainTensorHomotopyLeft (P.mapCompHomotopy P' P'' f.1.hom g.1.hom) _).trans
        (cochainTensorHomotopyRight _ (Q.mapCompHomotopy Q' Q'' f.2.hom g.2.hom)))

/-- Compute the derived tensor using any specified bounded-above projective models. -/
def boundedAboveDerivedTensorModelIso
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R))
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj) :
    ((boundedAboveDerivedTensor.obj (X, Y)).obj) ≅
      DerivedCategory.Q.obj (cochainTensor P.complex Q.complex) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel Y
  have := A.map_quasiIso P (𝟙 X.obj)
  have := B.map_quasiIso Q (𝟙 Y.obj)
  have := cochainTensorMap_quasiIso_of_KProjective (A.map P (𝟙 X.obj)) (B.map Q (𝟙 Y.obj))
  exact asIso (DerivedCategory.Q.map (cochainTensorMap (A.map P (𝟙 X.obj)) (B.map Q (𝟙 Y.obj))))

/-- Model computation respects arbitrary chain representatives of the two derived morphisms. -/
lemma boundedAboveDerivedTensorModelIso_naturality
    {X X' Y Y' : DerivedCategory.Minus (ModuleCat.{u} R)}
    (P : BoundedAboveDerivedModel X.obj) (P' : BoundedAboveDerivedModel X'.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (Q' : BoundedAboveDerivedModel Y'.obj)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : P.complex ⟶ P'.complex) (k : Q.complex ⟶ Q'.complex)
    (hh : DerivedCategory.Q.map h ≫ P'.iso.hom = P.iso.hom ≫ f.hom)
    (hk : DerivedCategory.Q.map k ≫ Q'.iso.hom = Q.iso.hom ≫ g.hom) :
    (boundedAboveDerivedTensor.map (f, g)).hom ≫
        (boundedAboveDerivedTensorModelIso X' Y' P' Q').hom =
      (boundedAboveDerivedTensorModelIso X Y P Q).hom ≫
        DerivedCategory.Q.map (cochainTensorMap h k) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel X'
  let C := boundedAboveDerivedChosenModel Y
  let D := boundedAboveDerivedChosenModel Y'
  have h₁ := (A.mapSquareHomotopy P B P' f.hom).trans
    ((P.mapHomotopyOfNaturality P' f.hom h hh).compLeft (A.map P (𝟙 _)))
  have h₂ := (C.mapSquareHomotopy Q D Q' g.hom).trans
    ((Q.mapHomotopyOfNaturality Q' g.hom k hk).compLeft (C.map Q (𝟙 _)))
  change DerivedCategory.Q.map (cochainTensorMap (A.map B f.hom) (C.map D g.hom)) ≫
      DerivedCategory.Q.map (cochainTensorMap (B.map P' (𝟙 _)) (D.map Q' (𝟙 _))) =
    DerivedCategory.Q.map (cochainTensorMap (A.map P (𝟙 _)) (C.map Q (𝟙 _))) ≫
      DerivedCategory.Q.map (cochainTensorMap h k)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cochainTensorMap_comp, cochainTensorMap_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
    ((cochainTensorHomotopyLeft h₁ _).trans (cochainTensorHomotopyRight _ h₂))

end SerrePositivity

end BoundedAboveDerivedTensorPart
