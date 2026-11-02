module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorClosedComparison

/-! # 全 Hom 自然性の閉零射への制限
概要：全 Hom 複体の自然性から、元の閉零射圏の自然変換を得る。
方針：単位からの射を前合成し、unitor の自然性で通常の合成を回収する。
規約：成分を変更しない。使われ方：実 dg 延長比較の四入力 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded

section Enriched
variable {V : Type u} [Category V] [MonoidalCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]

/-- 後合成の豊穣作用は、単位からの元に対して通常の合成を回収する。 -/
lemma dgClosedHom_postcompose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V f ≫ eHomWhiskerLeft V X g = eHomEquiv V (f ≫ g) := by
  rw [eHomWhiskerLeft, ← Category.assoc, rightUnitor_inv_naturality,
    Category.assoc, ← tensorHom_def_assoc, ← unitors_inv_equal, ← eHomEquiv_comp]

/-- 前合成の豊穣作用も、単位からの元に対して通常の合成を回収する。 -/
lemma dgClosedHom_precompose {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V g ≫ eHomWhiskerRight V f Z = eHomEquiv V (f ≫ g) := by
  rw [eHomWhiskerRight, ← Category.assoc, leftUnitor_inv_naturality,
    Category.assoc, ← tensorHom_def'_assoc, ← eHomEquiv_comp]
end Enriched

variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] (F G : DGFunctor A D E)

/-- 全 Hom 自然な元の閉零射族は、通常の閉零射について自然。 -/
lemma dgFunctorClosedComparison_naturality
    (a : ∀ x : D, ForgetEnrichment.of (Complex A) (F.obj x) ⟶
      ForgetEnrichment.of (Complex A) (G.obj x))
    (h : ∀ x y : D, F.map x y ≫
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (F.obj x)) (a y) =
      G.map x y ≫
        eHomWhiskerRight (Complex A) (a x) (ForgetEnrichment.of (Complex A) (G.obj y)))
    {x y : ClosedCategory A D} (f : x ⟶ y) :
    F.onClosed.map f ≫ a (ForgetEnrichment.to (Complex A) y) =
      a (ForgetEnrichment.to (Complex A) x) ≫ G.onClosed.map f := by
  apply (eHomEquiv (Complex A)).injective
  rw [← dgClosedHom_postcompose, ← dgClosedHom_precompose]
  exact congrArg (fun k => ForgetEnrichment.homTo (Complex A) f ≫ k)
    (h (ForgetEnrichment.to (Complex A) x) (ForgetEnrichment.to (Complex A) y))

end SerrePositivity.KST.SConstruction
