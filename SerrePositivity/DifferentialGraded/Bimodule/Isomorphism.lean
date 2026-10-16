module
public import SerrePositivity.DifferentialGraded.Bimodule.Evaluation
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedIso

/-! # 全Hom自然な同型族からの閉零bimodule同型 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 全Hom自然な右加群同型族から、閉零bimodule圏の同型を構成する。 -/
def isoOfFamily {M N : BimoduleCategory A B C}
    (a : ∀ c, (evaluation A B C c).obj M ≅ (evaluation A B C c).obj N)
    (h : ∀ c c', (underlying A B C M).toFunctor.map c c' ≫
      moduleHomPostcompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') ((underlying A B C N).rightAt c') (a c').hom =
      (underlying A B C N).toFunctor.map c c' ≫
      moduleHomPrecompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C N).rightAt c') (a c).hom) :
    M ≅ N where
  hom := ⟨fun c => (a c).hom, h⟩
  inv := ⟨fun c => (a c).inv, Bimodule.isoFamily_inv_naturality A B C a h⟩
  hom_inv_id := by
    apply Subtype.ext
    funext c
    exact (a c).hom_inv_id
  inv_hom_id := by
    apply Subtype.ext
    funext c
    exact (a c).inv_hom_id

@[simp]
lemma isoOfFamily_hom_eval {M N : BimoduleCategory A B C} (a) (h) (c : C) :
    (evaluation A B C c).map (isoOfFamily A B C (M := M) (N := N) a h).hom =
      (a c).hom := rfl

@[simp]
lemma isoOfFamily_inv_eval {M N : BimoduleCategory A B C} (a) (h) (c : C) :
    (evaluation A B C c).map (isoOfFamily A B C (M := M) (N := N) a h).inv =
      (a c).inv := rfl

end SerrePositivity.DifferentialGraded.BimoduleCategory
