module
public import SerrePositivity.KST.SConstruction.DGFunctorHomWhiskering
public import SerrePositivity.KST.SConstruction.DGConjugationNaturality
public import SerrePositivity.KST.SConstruction.DGFunctorHomUniversal

/-! # 全パラメータ自然変換の閉零射と同型に関する自然性
概要：任意 K の dg 自然変換は、元の閉零射と実同型を横切る全 Hom の式を満たす。
方針：全豊穣自然性に閉零射を挿入し、braiding と unitors の自然性を使う。
規約：単位パラメータへ制限しない。使われ方：ラベル付き入力作用の前合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
section Enriched
variable (V : Type u) [Category V] [MonoidalCategory V] [BraidedCategory V]
  {C : Type v} [Category C] [EnrichedOrdinaryCategory V C]
  {D : Type w} [Category D] [EnrichedOrdinaryCategory V D]
  {F G : EnrichedFunctor V C D}

/-- 全豊穣自然性へ閉零射を挿入すると、元の Hom 前後合成の可換式が得られる。 -/
lemma enrichedParameter_closed_naturality {K : V}
    (τ : GradedNatTrans ((Center.ofBraided V).obj K) F G) {X Y : C} (f : X ⟶ Y)
    (fF : F.obj X ⟶ F.obj Y) (fG : G.obj X ⟶ G.obj Y)
    (hF : eHomEquiv V f ≫ F.map X Y = eHomEquiv V fF)
    (hG : eHomEquiv V f ≫ G.map X Y = eHomEquiv V fG) :
    τ.app X ≫ eHomWhiskerLeft V (F.obj X) fG =
      τ.app Y ≫ eHomWhiskerRight V fF (G.obj Y) := by
  have h := congrArg (fun k =>
    (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eHomEquiv V f) ≫ k) (τ.naturality X Y)
  change (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eHomEquiv V f) ≫ (β_ K (X ⟶[V] Y)).hom ≫
      (F.map X Y ⊗ₘ τ.app Y) ≫ eComp V _ _ _ =
    (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eHomEquiv V f) ≫
      (τ.app X ⊗ₘ G.map X Y) ≫ eComp V _ _ _ at h
  simp only [BraidedCategory.braiding_naturality_assoc, tensorHom_comp_tensorHom_assoc,
    Category.id_comp] at h
  rw [rightUnitor_inv_braiding_assoc, hF, hG] at h
  have hR : τ.app X ≫ eHomWhiskerLeft V (F.obj X) fG =
      (ρ_ K).inv ≫ (τ.app X ⊗ₘ eHomEquiv V fG) ≫ eComp V _ _ _ := by
    rw [eHomWhiskerLeft, rightUnitor_inv_naturality_assoc, tensorHom_def]
    simp only [Category.assoc]
    rfl
  have hL : τ.app Y ≫ eHomWhiskerRight V fF (G.obj Y) =
      (λ_ K).inv ≫ (eHomEquiv V fF ⊗ₘ τ.app Y) ≫ eComp V _ _ _ := by
    rw [eHomWhiskerRight, leftUnitor_inv_naturality_assoc, tensorHom_def']
    simp only [Category.assoc]
    rfl
  exact hR.trans (h.symm.trans hL.symm)
end Enriched

variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] {F G : DGFunctor A C D}

/-- 任意 K の dg 自然変換は、入力の元の閉零射に対して全 Hom で自然。 -/
lemma dgFunctorParameter_closed_naturality {K : Complex A}
    (τ : DGFunctorParamTrans A C D K F G) {X Y : ClosedCategory A C} (f : X ⟶ Y) :
    τ.app (ForgetEnrichment.to (Complex A) X) ≫
        eHomWhiskerLeft (Complex A) (F.onClosed.obj X) (G.onClosed.map f) =
      τ.app (ForgetEnrichment.to (Complex A) Y) ≫
        eHomWhiskerRight (Complex A) (F.onClosed.map f) (G.onClosed.obj Y) :=
  enrichedParameter_closed_naturality (Complex A)
    (F := dgFunctorClosedBoth A F) (G := dgFunctorClosedBoth A G)
    { app := fun X => τ.app (ForgetEnrichment.to (Complex A) X),
      naturality := fun _ _ => τ.naturality _ _ } f _ _ rfl rfl

/-- 任意 K の作用は、入力の元の閉零同型の両端の像による共役と可換。 -/
lemma dgFunctorParameter_conjugation {K : Complex A}
    (τ : DGFunctorParamTrans A C D K F G) {X Y : ClosedCategory A C} (e : X ≅ Y) :
    τ.app (ForgetEnrichment.to (Complex A) X) ≫ enrichedClosedIsoConjugation (Complex A)
        (F.onClosed.mapIso e) (G.onClosed.mapIso e) =
      τ.app (ForgetEnrichment.to (Complex A) Y) :=
  enrichedConjugation_of_naturality (Complex A) _ _ _ _
    (dgFunctorParameter_closed_naturality A τ e.hom)

end SerrePositivity.KST.SConstruction
