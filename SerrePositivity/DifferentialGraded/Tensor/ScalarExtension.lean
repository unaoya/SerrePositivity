module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCoherence
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # dg 圏の underived 係数変更

同じ対象に、係数拡大した Hom を置く。Mathlib の豊穣構造の移送を使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory Limits MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- 非有界複体の係数拡大は強モノイダル。平坦性を仮定しない。 -/
instance extensionMonoidal : (extension φ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.mk'
      (εIso := (unitIso φ).symm)
      (μIso := fun K L => (tensorIso φ K L).symm)
      (μIso_inv_natural_left := fun f L => by
        simpa using (tensorIso_naturality φ f (𝟙 L)).symm)
      (μIso_inv_natural_right := fun K f => by
        simpa using (tensorIso_naturality φ (𝟙 K) f).symm)
      (oplax_associativity := tensorIso_associator φ)
      (oplax_left_unitality := tensorIso_left_unitor φ)
      (oplax_right_unitality := tensorIso_right_unitor φ))

/-- 対象は D のまま、Hom を係数拡大する Mathlib の型別名。 -/
abbrev DGBaseChange (D : Type v) [DGCategory A D] := TransportEnrichment (extension φ) D

variable (D : Type v) [DGCategory A D]

lemma homObject_eq (x y : DGBaseChange φ D) :
    homObject A' (DGBaseChange φ D) x y = (extension φ).obj (homObject A D x y) := rfl

lemma identity_eq (x : DGBaseChange φ D) :
    eId (Complex A') x = (unitIso φ).inv ≫ (extension φ).map (eId (Complex A) (C := D) x) := rfl

lemma composition_eq (x y z : DGBaseChange φ D) :
    eComp (Complex A') x y z = (tensorIso φ (homObject A D x y) (homObject A D y z)).inv ≫
      (extension φ).map (eComp (Complex A) (C := D) x y z) := rfl

variable {D} {E : Type w} [DGCategory A E]

/-- dg 関手にも Hom ごとに係数拡大を施す。 -/
def dgFunctor (F : DGFunctor A D E) :
    DGFunctor A' (DGBaseChange φ D) (DGBaseChange φ E) where
  obj := F.obj
  map x y := (extension φ).map (F.map x y)
  map_id x := by
    change (unitIso φ).inv ≫ (extension φ).map (eId (Complex A) (C := D) x) ≫
      (extension φ).map (F.map x x) = _
    rw [← Functor.map_comp, F.map_id]
    rfl
  map_comp x y z := by
    change (tensorIso φ _ _).inv ≫ (extension φ).map (eComp (Complex A) (C := D) x y z) ≫
      (extension φ).map (F.map x z) = _
    rw [← Functor.map_comp, F.map_comp, Functor.map_comp]
    change Functor.LaxMonoidal.μ (extension φ) _ _ ≫
      (extension φ).map (F.map x y ⊗ₘ F.map y z) ≫ _ = _
    rw [← Functor.LaxMonoidal.μ_natural_assoc]
    rfl

end SerrePositivity.DifferentialGraded.ScalarExtension
