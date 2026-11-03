module
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 元の Yoneda 全 Hom 同型を逆に読む End 関手
概要：元の代表加群の End を、元の dg 対象の End へ厳密に戻す。
方針：構成済み Yoneda Hom 同型の順射と、元の Yoneda 関手の単位・合成式を使う。
規約：全 Hom 複体で戻す。使われ方：商 End から元の右対象 End への比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D] (b : D)

/-- 元の Yoneda Hom 同型を逆に使う写像は、元の二つの単位を保つ。 -/
lemma dgEndYonedaInverseHom_unit :
    eId (Complex R) (representable R b) ≫ (dgYonedaIso R b (representable R b)).hom =
      eId (Complex R) b := by
  have h : eId (Complex R) b ≫ (dgYonedaIso R b (representable R b)).inv =
      eId (Complex R) (representable R b) := (dgYoneda R D).map_id b
  have he := congrArg (fun f => f ≫ (dgYonedaIso R b (representable R b)).hom) h
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he
  exact he.symm

/-- 同じ全 Hom 同型の逆向きは、元の豊穣合成も厳密に保つ。 -/
lemma dgEndYonedaInverseHom_comp :
    eComp (Complex R) (representable R b) (representable R b) (representable R b) ≫
        (dgYonedaIso R b (representable R b)).hom =
      ((dgYonedaIso R b (representable R b)).hom ⊗ₘ
        (dgYonedaIso R b (representable R b)).hom) ≫ eComp (Complex R) b b b := by
  let i := dgYonedaIso R b (representable R b)
  have hc : eComp (Complex R) b b b ≫ i.inv =
      (i.inv ⊗ₘ i.inv) ≫
        eComp (Complex R) (representable R b) (representable R b) (representable R b) :=
    (dgYoneda R D).map_comp b b b
  apply (cancel_epi (i.inv ⊗ₘ i.inv)).1
  change (i.inv ⊗ₘ i.inv) ≫
      (eComp (Complex R) (representable R b) (representable R b) (representable R b) ≫
        i.hom) = (i.inv ⊗ₘ i.inv) ≫ ((i.hom ⊗ₘ i.hom) ≫ eComp (Complex R) b b b)
  calc
    _ = (eComp (Complex R) b b b ≫ i.inv) ≫ i.hom := by
      rw [← Category.assoc, ← hc]
    _ = eComp (Complex R) b b b := by
      rw [Category.assoc, i.inv_hom_id, Category.comp_id]
    _ = _ := by
      simp only [← Category.assoc, tensorHom_comp_tensorHom, i.inv_hom_id,
        id_tensorHom_id, Category.id_comp]

/-- 元の代表加群の End から元の dg 対象の End へ戻す実 dg 関手。 -/
def dgEndYonedaInverse :
    DGFunctor R (EndomorphismObject (representable R b)) (EndomorphismObject b) where
  obj _ := .point
  map _ _ := (dgYonedaIso R b (representable R b)).hom
  map_id _ := dgEndYonedaInverseHom_unit R D b
  map_comp _ _ _ := dgEndYonedaInverseHom_comp R D b

/-- 同じ End 関手の全 Hom 写像は、元の Yoneda Hom 同型の順射。 -/
lemma dgEndYonedaInverse_map (x y : EndomorphismObject (representable R b)) :
    (dgEndYonedaInverse R D b).map x y = (dgYonedaIso R b (representable R b)).hom := rfl

/-- 同じ実 End 逆向き写像は、全 Hom 複体の同型である。 -/
lemma dgEndYonedaInverse_map_isIso (x y : EndomorphismObject (representable R b)) :
    IsIso ((dgEndYonedaInverse R D b).map x y) := by
  change IsIso (dgYonedaIso R b (representable R b)).hom
  infer_instance

end SerrePositivity.KST.SConstruction
