module
public import SerrePositivity.DifferentialGraded.Functor.Basic
public import SerrePositivity.DifferentialGraded.Category.Components
public import SerrePositivity.DifferentialGraded.Complexes.Currying

/-! # 斉次成分の単位・合成式からのdg関手構成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- Homのchain mapに対して斉次単位・合成式を与える構成子。 -/
def ofHomMaps (F : D → E) (H : ∀ x y, (x ⟶[Complex A] y) ⟶ (F x ⟶[Complex A] F y))
    (hi : ∀ x, (H x x).f 0 (unitElement A x).val = (unitElement A (F x)).val)
    (hc : ∀ (x y z : D) (p q n : ℤ) (hn : p + q = n)
      (f : GradedHom A x y p) (g : GradedHom A y z q),
      (H x z).f n (forward A f g hn) =
        forward A ((H x y).f p f) ((H y z).f q g) hn) : DGFunctor A D E where
  obj := F
  map := H
  map_id x := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (eId (Complex A) x ≫ H x x)).val =
      (cycleFromUnit _ (eId (Complex A) (F x))).val
    rw [cycleFromUnit_postcomp]
    exact hi x
  map_comp x y z := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (H x z).f n (forward A f g hn) =
      (eComp (Complex A) (F x) (F y) (F z)).f n
        ((H x y ⊗ₘ H y z).f n
          (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    rw [tensorMap_apply]
    exact hc x y z p q n hn f g

/-- dg関手は単位の零次数cycleを保存する。 -/
lemma map_unitElement (F : DGFunctor A D E) (x : D) :
    (F.map x x).f 0 (unitElement A x).val = (unitElement A (F.obj x)).val := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (F.map_id x)
  rw [cycleFromUnit_postcomp] at h
  exact h

/-- dg関手は任意次数の豊穣順合成を保存する。 -/
lemma map_forward (F : DGFunctor A D E) {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    (F.map x z).f n (forward A f g hn) =
      forward A ((F.map x y).f p f) ((F.map y z).f q g) hn := by
  have h := congrArg (fun l => l.f n
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g)))
    (F.map_comp x y z)
  change (F.map x z).f n (forward A f g hn) =
    (eComp (Complex A) (F.obj x) (F.obj y) (F.obj z)).f n
      ((F.map x y ⊗ₘ F.map y z).f n
        (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n hn (f ⊗ₜ[A] g))) at h
  rw [tensorMap_apply] at h
  exact h

end SerrePositivity.DifferentialGraded.DGFunctor
