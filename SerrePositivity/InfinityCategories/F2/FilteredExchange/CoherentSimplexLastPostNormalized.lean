module

public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentSimplexLastPostCoordinates

/-!
概要：最後の指定後合成の作用を、任意の同じ標準端点で照合する。
方針：既存の Hom 座標に同じ端点等式を続け、等号の射を合成する。
規約：元の Hom と指定後合成を保持。使われ方：元の合成 prism との全 Hom 照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 共通の標準端点での一致から、元の二端点の表示変更を含む一致を回収する。 -/
lemma simplicialHom_eq_of_normalized {A B A' B' X Y : C} {P : SSet.{u}}
    (hA : A = A') (hB : B = B') (cA : A' = X) (cB : B' = Y)
    (f : P ⟶ SimplicialCategory.sHom A B) (g : P ⟶ SimplicialCategory.sHom A' B')
    (e : f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans cA) (hB.trans cB)) =
      g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom cA cB)) :
    f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) = g := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom cA cB))).1
  simpa only [Category.assoc, eqToHom_trans] using e

/-- 旧二対象間の全 Hom は、任意の同じ標準端点で元の作用に一致する。 -/
lemma coherentSimplexLastPostHom_cast_cast_normalized {n : ℕ}
    (s : (SimplicialNerve C) _⦋n + 1⦌) {Y A B : C}
    (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y) (i j : Fin (n + 1))
    (hi : s.obj ⟨ULift.up i.castSucc⟩ = A) (hj : s.obj ⟨ULift.up j.castSucc⟩ = B) :
    coherentSimplexLastPostHom s g i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        ((coherentSimplexLastPostObj_cast s i).trans hi)
        ((coherentSimplexLastPostObj_cast s j).trans hj)) =
    s.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hi hj) := by
  have e := congrArg (fun k => k ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hi hj))
    (coherentSimplexLastPostHom_cast_cast s g i j)
  simpa only [Category.assoc, eqToHom_trans] using e

/-- 最後への全 Hom は、標準端点でも元の作用への同じ指定後合成。 -/
lemma coherentSimplexLastPostHom_cast_last_normalized {n : ℕ}
    (s : (SimplicialNerve C) _⦋n + 1⦌) {Y A B : C} (i : Fin (n + 1))
    (hi : s.obj ⟨ULift.up i.castSucc⟩ = A)
    (hl : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ = B) (g : B ⟶ Y) :
    coherentSimplexLastPostHom s (eqToHom hl ≫ g) i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        ((coherentSimplexLastPostObj_cast s (Y := Y) i).trans hi)
        (coherentSimplexLastPostObj_last s (Y := Y))) =
    (s.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hi hl)) ≫ eHomWhiskerLeft SSet A g := by
  have e := congrArg (fun k => k ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom hi (rfl : Y = Y)))
    (coherentSimplexLastPostHom_cast_last s (eqToHom hl ≫ g) i)
  simp only [Category.assoc] at e
  rw [simplicialHom_postcomp_display hi hl g] at e
  simpa only [Category.assoc, eqToHom_trans] using e

end SerrePositivity.InfinityCategories.F2
