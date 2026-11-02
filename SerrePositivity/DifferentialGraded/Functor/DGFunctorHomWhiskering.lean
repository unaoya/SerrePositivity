module
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation

/-! # dg 関手の全 Hom 作用と閉零前後合成
概要：dg 関手の全次数 Hom 作用が、元の閉零射による前後合成と可換である。
方針：抽象豊穣関手の合成保存と unitor の自然性から証明する。
規約：閉零射の自然性だけで全 Hom の式を代用しない。使われ方：Perf 作用の合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
section Enriched
variable (V : Type u) [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]
  {D : Type w} [Category D] [EnrichedOrdinaryCategory V D]
  (F : EnrichedFunctor V C D)

/-- 豊穣 Hom 作用は、その単位元上の像に対応する射の後合成と可換。 -/
lemma enrichedFunctorHom_postcompose {Y Y' : C} (g : Y ⟶ Y')
    (g' : F.obj Y ⟶ F.obj Y')
    (h : eHomEquiv V g ≫ F.map Y Y' = eHomEquiv V g') (X : C) :
    eHomWhiskerLeft V X g ≫ F.map X Y' =
      F.map X Y ≫ eHomWhiskerLeft V (F.obj X) g' := by
  simp only [eHomWhiskerLeft, Category.assoc]
  rw [F.map_comp]
  simp only [tensorHom_def', Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, h, whisker_exchange_assoc,
    ← rightUnitor_inv_naturality_assoc]

/-- 豊穣 Hom 作用は、その単位元上の像に対応する射の前合成とも可換。 -/
lemma enrichedFunctorHom_precompose {X X' : C} (g : X ⟶ X')
    (g' : F.obj X ⟶ F.obj X')
    (h : eHomEquiv V g ≫ F.map X X' = eHomEquiv V g') (Y : C) :
    eHomWhiskerRight V g Y ≫ F.map X Y =
      F.map X' Y ≫ eHomWhiskerRight V g' (F.obj Y) := by
  simp only [eHomWhiskerRight, Category.assoc]
  rw [F.map_comp]
  simp only [tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, h, ← whisker_exchange_assoc,
    ← leftUnitor_inv_naturality_assoc]
end Enriched

variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] (F : DGFunctor A C D)

/-- 始域と標的を同じ閉零対象で表示した、元の全 Hom 作用。 -/
def dgFunctorClosedBoth :
    EnrichedFunctor (Complex A) (ClosedCategory A C) (ClosedCategory A D) where
  obj X := ForgetEnrichment.of (Complex A) (F.obj (ForgetEnrichment.to (Complex A) X))
  map X Y := F.map (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y)
  map_id X := F.map_id (ForgetEnrichment.to (Complex A) X)
  map_comp X Y Z := F.map_comp (ForgetEnrichment.to (Complex A) X)
    (ForgetEnrichment.to (Complex A) Y) (ForgetEnrichment.to (Complex A) Z)

/-- 元の dg 関手の全 Hom 作用は、元の閉零射の後合成と可換。 -/
lemma dgFunctorHom_postcompose {Y Y' : ClosedCategory A C} (g : Y ⟶ Y')
    (X : ClosedCategory A C) :
    eHomWhiskerLeft (Complex A) X g ≫
        F.map (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y') =
      F.map (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y) ≫
        eHomWhiskerLeft (Complex A) (F.onClosed.obj X) (F.onClosed.map g) :=
  enrichedFunctorHom_postcompose (Complex A) (dgFunctorClosedBoth A F) g
    (F.onClosed.map g) rfl X

/-- 元の dg 関手の全 Hom 作用は、元の閉零射の前合成と可換。 -/
lemma dgFunctorHom_precompose {X X' : ClosedCategory A C} (g : X ⟶ X')
    (Y : ClosedCategory A C) :
    eHomWhiskerRight (Complex A) g Y ≫
        F.map (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y) =
      F.map (ForgetEnrichment.to (Complex A) X') (ForgetEnrichment.to (Complex A) Y) ≫
        eHomWhiskerRight (Complex A) (F.onClosed.map g) (F.onClosed.obj Y) :=
  enrichedFunctorHom_precompose (Complex A) (dgFunctorClosedBoth A F) g
    (F.onClosed.map g) rfl Y

end SerrePositivity.KST.SConstruction
