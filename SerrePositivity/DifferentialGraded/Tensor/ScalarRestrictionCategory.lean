module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarRestrictionHom

/-! # dg 圏の係数制限と係数変更の単位 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

abbrev DGRestriction (C : Type v) [DGCategory A' C] := TransportEnrichment (restriction φ) C

def restrictDGFunctor {C : Type v} {E : Type w} [DGCategory A' C] [DGCategory A' E]
    (F : DGFunctor A' C E) : DGFunctor A (DGRestriction φ C) (DGRestriction φ E) where
  obj := F.obj
  map x y := (restriction φ).map (F.map x y)
  map_id x := by
    change Functor.LaxMonoidal.ε (restriction φ) ≫
      (restriction φ).map (eId (Complex A') (C := C) x) ≫ (restriction φ).map (F.map x x) = _
    rw [← CategoryTheory.Functor.map_comp, F.map_id]
    rfl
  map_comp x y z := by
    change Functor.LaxMonoidal.μ (restriction φ) _ _ ≫
      (restriction φ).map (eComp (Complex A') (C := C) x y z) ≫
        (restriction φ).map (F.map x z) = _
    rw [← CategoryTheory.Functor.map_comp, F.map_comp, CategoryTheory.Functor.map_comp,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    rfl

/-- モノイダル随伴の単位は、dg 圏の Hom の係数変更への dg 関手を与える。 -/
def unitDGFunctor (D : Type v) [DGCategory A D] :
    DGFunctor A D (DGRestriction φ (DGBaseChange φ D)) where
  obj x := x
  map x y := (adjunction φ).unit.app (homObject A D x y)
  map_id x := by
    have hu := NatTrans.IsMonoidal.unit (τ := (adjunction φ).unit)
    change 𝟙 _ ≫ (adjunction φ).unit.app (𝟙_ (Complex A)) =
      Functor.LaxMonoidal.ε (restriction φ) ≫ (restriction φ).map (unitIso φ).inv at hu
    rw [Category.id_comp] at hu
    change eId (Complex A) (C := D) x ≫ (adjunction φ).unit.app _ =
      Functor.LaxMonoidal.ε (restriction φ) ≫
        (restriction φ).map ((unitIso φ).inv ≫ (extension φ).map (eId (Complex A) (C := D) x))
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← hu]
    exact (adjunction φ).unit.naturality (eId (Complex A) (C := D) x)
  map_comp x y z := by
    have ht := NatTrans.IsMonoidal.tensor (τ := (adjunction φ).unit)
      (homObject A D x y) (homObject A D y z)
    change 𝟙 _ ≫ (adjunction φ).unit.app (homObject A D x y ⊗ homObject A D y z) =
      ((adjunction φ).unit.app (homObject A D x y) ⊗ₘ
        (adjunction φ).unit.app (homObject A D y z)) ≫
      Functor.LaxMonoidal.μ (restriction φ) _ _ ≫
        (restriction φ).map (tensorIso φ _ _).inv at ht
    rw [Category.id_comp] at ht
    change eComp (Complex A) (C := D) x y z ≫ (adjunction φ).unit.app _ =
      ((adjunction φ).unit.app (homObject A D x y) ⊗ₘ
        (adjunction φ).unit.app (homObject A D y z)) ≫
      Functor.LaxMonoidal.μ (restriction φ) _ _ ≫
        (restriction φ).map ((tensorIso φ _ _).inv ≫
          (extension φ).map (eComp (Complex A) (C := D) x y z))
    rw [CategoryTheory.Functor.map_comp]
    exact ((adjunction φ).unit.naturality (eComp (Complex A) (C := D) x y z)).trans
      (by
        have ht' := congrArg (fun t => t ≫ (restriction φ).map ((extension φ).map
          (eComp (Complex A) (C := D) x y z))) ht
        simp only [Category.assoc] at ht'
        convert ht' using 1 <;> rfl)

end SerrePositivity.DifferentialGraded.ScalarExtension
