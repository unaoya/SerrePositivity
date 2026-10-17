module
public import SerrePositivity.DifferentialGraded.Bimodule.PairedRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.ExplicitRightModuleFunctor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestriction

/-! # 直接両端制限と積dg圏上の既存制限の表示比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A D B) (G : DGFunctor A E C)

/-- 直接両端制限と積dg関手制限の、値で恒等となる全Hom自然な表示比較。 -/
def pairedRestrictionPresentationObjIso (P : BimoduleCategory A B C) :
    (rightModuleFunctor A D E).obj
        ((BimoduleCategory.pairedRestrictionFunctor A B C D E F G).obj P) ≅
      (moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (bimoduleRestrictionIndex A D E B C F G)).obj ((rightModuleFunctor A B C).obj P) :=
  moduleIsoMk A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (fun _ => Iso.refl _) (by
    intro x y
    apply hom_naturality_of_apply
    intro p f
    refine (CochainComplex.HomComplex.Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (CochainComplex.HomComplex.Cochain.id_comp _).symm
    change ((𝟙 _ ≫
      (Bimodule.rightRestriction A B D E F
        (Bimodule.leftRestriction A B C E G (BimoduleCategory.underlying A B C P))).uncurryHom
          x.unop.unop y.unop.unop).f p f) =
      (((F.op.map x.unop.unop.1 y.unop.unop.1 ⊗ₘ G.map x.unop.unop.2 y.unop.unop.2) ≫
        (𝟙 _ ≫ (BimoduleCategory.underlying A B C P).uncurryHom
          (F.op.obj x.unop.unop.1, G.obj x.unop.unop.2)
          (F.op.obj y.unop.unop.1, G.obj y.unop.unop.2))).f p f)
    simp only [Category.id_comp]
    exact congrArg (fun k => k.f p f) (Bimodule.pairedRestriction_uncurryHom A B C D E F G
      (BimoduleCategory.underlying A B C P) x.unop.unop y.unop.unop))

@[simp]
lemma pairedRestrictionPresentationObjIso_hom_eval (P : BimoduleCategory A B C)
    (x : (DGTensorCategory A Dᵒᵖ E)ᵒᵖ) :
    (moduleEvaluation A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ x).map
        (pairedRestrictionPresentationObjIso A B C D E F G P).hom = 𝟙 _ :=
  moduleIsoMk_hom_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ _ _ x

/-- 両端制限の表示squareは任意の閉零bimodule射に自然。 -/
def pairedRestrictionPresentationIso :
    BimoduleCategory.pairedRestrictionFunctor A B C D E F G ⋙ rightModuleFunctor A D E ≅
      rightModuleFunctor A B C ⋙
        moduleRestriction A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          (bimoduleRestrictionIndex A D E B C F G) :=
  NatIso.ofComponents (pairedRestrictionPresentationObjIso A B C D E F G) (by
    intro P Q q
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, pairedRestrictionPresentationObjIso_hom_eval,
      Functor.comp_map]
    have h := rightModuleFunctor_map_value A D E
      ((BimoduleCategory.pairedRestrictionFunctor A B C D E F G).map q)
      x.unop.1.unop x.unop.2
    have h' := moduleRestriction_map_eval A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
      (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (bimoduleRestrictionIndex A D E B C F G)
      ((rightModuleFunctor A B C).map q) x
    exact h.trans ((BimoduleCategory.pairedRestrictionFunctor_map_value A B C D E F G q
      x.unop.1.unop x.unop.2).trans
        ((rightModuleFunctor_map_value A B C q (F.obj x.unop.1.unop)
          (G.obj x.unop.2)).symm.trans h'.symm)))

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
