module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentSimplexLastPostData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCoordinates

/-!
概要：最後の指定後合成の Hom データを、元の対象の表示へ正規化する。
方針：分岐の端点等式と、その同じ Hom の表示変更を明示する。
規約：指定射の後合成を保持。使われ方：豊穣関手の単位・合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}

/-- 最後の対象は指定射の終域。 -/
lemma coherentSimplexLastPostObj_last :
    coherentSimplexLastPostObj s (Y := Y) (Fin.last (n + 1)) = Y := by
  simp only [coherentSimplexLastPostObj, Fin.lastCases_last]
/-- 旧対象は厳密に保持される。 -/
lemma coherentSimplexLastPostObj_cast (i : Fin (n + 1)) :
    coherentSimplexLastPostObj s (Y := Y) i.castSucc = s.obj ⟨ULift.up i.castSucc⟩ := by
  simp only [coherentSimplexLastPostObj, Fin.lastCases_castSucc]

variable (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)

/-- 指定した始点・終点の表示変更は同じ後合成作用と可換。 -/
lemma simplicialHom_postcomp_display {A A' B B' D : C}
    (hA : A = A') (hB : B = B') (f : B' ⟶ D) :
    eHomWhiskerLeft SSet A (eqToHom hB ≫ f) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA (rfl : D = D)) =
      eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) ≫
        eHomWhiskerLeft SSet A' f := by
  cases hA
  cases hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 最後の自己 Hom の正規化は同じ豊穣恒等。 -/
lemma coherentSimplexLastPostHom_last_last :
    coherentSimplexLastPostHom s g (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentSimplexLastPostObj_last s) (coherentSimplexLastPostObj_last s)) =
      toUnit _ ≫ eId SSet Y := by
  simp -implicitDefEqProofs +instances [coherentSimplexLastPostHom,
    coherentSimplexLastPostObj_last, Category.assoc]
/-- 旧二対象間の全 Hom の正規化は元の作用。 -/
lemma coherentSimplexLastPostHom_cast_cast (i j : Fin (n + 1)) :
    coherentSimplexLastPostHom s g i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentSimplexLastPostObj_cast s i) (coherentSimplexLastPostObj_cast s j)) =
      s.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ := by
  simp -implicitDefEqProofs +instances [coherentSimplexLastPostHom,
    coherentSimplexLastPostObj_cast, Category.assoc]
/-- 最後へ入る全 Hom の正規化は元の作用に指定射を後合成した値。 -/
lemma coherentSimplexLastPostHom_cast_last (i : Fin (n + 1)) :
    coherentSimplexLastPostHom s g i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentSimplexLastPostObj_cast s i) (coherentSimplexLastPostObj_last s)) =
      s.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫
        eHomWhiskerLeft SSet (s.obj ⟨ULift.up i.castSucc⟩) g := by
  simp -implicitDefEqProofs +instances [coherentSimplexLastPostHom,
    coherentSimplexLastPostObj_cast, coherentSimplexLastPostObj_last, Category.assoc]

end SerrePositivity.InfinityCategories.F2
