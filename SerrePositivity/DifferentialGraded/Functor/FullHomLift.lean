module
public import SerrePositivity.DifferentialGraded.Functor.Basic
/-!
概要：全 Hom 鎖写像が同型である dg 関手に沿って、指定された関手成分を持ち上げる。
方針：同じ対象ラベルで Hom の逆鎖写像を合成し、単位・合成を同型の単射性で反映する。
規約：対象の全射性を仮定せず、指定対象写像と元の全 Hom 成分を入力に保持する。
使われ方：c′ の実係数閉包から固定基底コードへ元の出発 dg 関手を輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (E : Type w) [DGCategory R E] (F : DGFunctor R D E)
  (hF : ∀ x y, IsIso (F.map x y))
  (C : Type z) [DGCategory R C] (obj : C → D)
  (map : ∀ x y, homObject R C x y ⟶ homObject R E (F.obj (obj x)) (F.obj (obj y)))
  (hu : ∀ x, eId (Complex R) x ≫ map x x = eId (Complex R) (F.obj (obj x)))
  (hc : ∀ x y z, eComp (Complex R) x y z ≫ map x z =
    (map x y ⊗ₘ map y z) ≫ eComp (Complex R) (F.obj (obj x)) (F.obj (obj y)) (F.obj (obj z)))

def dgFunctorFullHomLift : DGFunctor R C D := by
  letI (x y : D) : IsIso (F.map x y) := hF x y
  exact
    { obj := obj
      map x y := map x y ≫ inv (F.map (obj x) (obj y))
      map_id x := by
        apply (cancel_mono (F.map (obj x) (obj x))).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        exact (hu x).trans (F.map_id (obj x)).symm
      map_comp x y z := by
        apply (cancel_mono (F.map (obj x) (obj z))).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [F.map_comp (obj x) (obj y) (obj z)]
        rw [tensorHom_comp_tensorHom_assoc]
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        exact hc x y z }

lemma dgFunctorFullHomLift_map (x y : C) :
    (dgFunctorFullHomLift R D E F hF C obj map hu hc).map x y ≫
      F.map (obj x) (obj y) = map x y := by
  letI (x y : D) : IsIso (F.map x y) := hF x y
  change (map x y ≫ inv (F.map (obj x) (obj y))) ≫ F.map (obj x) (obj y) = _
  simp

end SerrePositivity.DifferentialGraded
