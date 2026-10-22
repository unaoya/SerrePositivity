module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTransport

/-!
双加群の閉元を対象とし、元の比較差の mapping cocone を Hom とする実 dg gluing 圏。
代表加群表示への全 Hom 鎖同型によって単位・合成・結合律を移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の全 Hom 複体に、単位・合成と実 dg 圏法則を与える。 -/
instance dgGluingDGCategory : DGCategory R (DGGluingObject R C D M) :=
  dgGluingHomIsoEnrichment R (DGGluingObject R C D M)
    (DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
    (dgGluingCommaObject R C D M) (dgGluingHomComplex R C D M)
    (dgGluingHomRepresentableIso R C D M)

/-- 実 dg gluing の全 Hom は定義した同じ mapping cocone。 -/
lemma dgGluing_hom (X Y : DGGluingObject R C D M) :
    homObject R (DGGluingObject R C D M) X Y = dgGluingHomComplex R C D M X Y := rfl

/-- 代表加群表示の comma への、全 Hom 鎖同型を持つ実 dg 関手。 -/
def dgGluingToComma :
    DGFunctor R (DGGluingObject R C D M)
      (DGFunctorCommaObject R D (RightModule R C) M.toFunctor) where
  obj := dgGluingCommaObject R C D M
  map := fun X Y ↦ (dgGluingHomRepresentableIso R C D M X Y).hom
  map_id X := by
    change (eId (Complex R) (dgGluingCommaObject R C D M X) ≫
      (dgGluingHomRepresentableIso R C D M X X).inv) ≫
      (dgGluingHomRepresentableIso R C D M X X).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  map_comp X Y Z := by
    change (((dgGluingHomRepresentableIso R C D M X Y).hom ⊗ₘ
      (dgGluingHomRepresentableIso R C D M Y Z).hom) ≫
      eComp (Complex R) (dgGluingCommaObject R C D M X)
        (dgGluingCommaObject R C D M Y) (dgGluingCommaObject R C D M Z) ≫
      (dgGluingHomRepresentableIso R C D M X Z).inv) ≫
      (dgGluingHomRepresentableIso R C D M X Z).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 右成分への実 dg 射影。 -/
def dgGluingRight : DGFunctor R (DGGluingObject R C D M) D :=
  (dgGluingToComma R C D M).comp (dgFunctorCommaSource R D (RightModule R C) M.toFunctor)

/-- 左成分の代表加群への実 dg 射影。 -/
def dgGluingLeftModule : DGFunctor R (DGGluingObject R C D M) (RightModule R C) :=
  (dgGluingToComma R C D M).comp (dgFunctorCommaReplacement R D (RightModule R C) M.toFunctor)

end SerrePositivity.InfinityCategories
