module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCover

/-!
概要：smart connective cover を実 dg 代数の関手にし、元の代数への自然な比較を構成する。
方針：切断複体の元の射を使い、包含の単射性で単位と積の保存を証明する。
規約：厳密な単位・合成と、元の underlying chain map を保持。
使われ方：connective な dg 代数の塔を、厳密な非正次数模型の塔へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex ComplexShape
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

def coverUnderlyingFunctor : Mon (Complex R) ⥤ Complex R :=
  Mon.forget (Complex R) ⋙ (embeddingUpIntLE 0).truncLEFunctor (ModuleCat R)

def connectiveCoverMap {B C : Mon (Complex R)} (f : B ⟶ C) :
    connectiveCover R B ⟶ connectiveCover R C := by
  let t := CochainComplex.truncLEMap f.hom 0
  have ht : t ≫ coverInclusion R C = coverInclusion R B ≫ f.hom :=
    CochainComplex.ιTruncLE_naturality f.hom 0
  refine Mon.Hom.mk' t ?_ ?_
  · apply (cancel_mono (coverInclusion R C)).1
    change (coverOne R B ≫ t) ≫ coverInclusion R C = coverOne R C ≫ coverInclusion R C
    rw [Category.assoc, ht, ← Category.assoc, coverOne_inclusion,
      IsMonHom.one_hom, coverOne_inclusion]
  · apply (cancel_mono (coverInclusion R C)).1
    change (coverMul R B ≫ t) ≫ coverInclusion R C =
      ((t ⊗ₘ t) ≫ coverMul R C) ≫ coverInclusion R C
    rw [Category.assoc, ht, ← Category.assoc, coverMul_inclusion]
    simp only [Category.assoc, coverMul_inclusion, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc, ht]

lemma connectiveCoverMap_hom {B C : Mon (Complex R)} (f : B ⟶ C) :
    (connectiveCoverMap R f).hom = (coverUnderlyingFunctor R).map f := rfl

def connectiveCoverFunctor : Mon (Complex R) ⥤ Mon (Complex R) where
  obj := connectiveCover R
  map := connectiveCoverMap R
  map_id B := by
    apply Mon.Hom.ext
    exact (coverUnderlyingFunctor R).map_id B
  map_comp f g := by
    apply Mon.Hom.ext
    exact (coverUnderlyingFunctor R).map_comp f g

def connectiveCoverCounit : connectiveCoverFunctor R ⟶ 𝟭 (Mon (Complex R)) where
  app := connectiveCoverInclusion R
  naturality {_ _} f := by
    apply Mon.Hom.ext
    exact CochainComplex.ιTruncLE_naturality f.hom 0

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
