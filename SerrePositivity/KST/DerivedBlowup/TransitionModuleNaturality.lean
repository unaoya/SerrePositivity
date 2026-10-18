module

public import SerrePositivity.KST.DerivedBlowup.TransitionModuleAction

/-!
概要：KST §3.1 の指定単位矢から得た加群比較の図式加群に関する自然性。
方針：全次数 Hom の自然性を指定単位矢で評価し、通常鎖写像への変換と合成の可換性を使う。
規約：各比較が dg 加群射であることに加えて、入力加群の射についても自然であると示す。
使われ方：比較射を自然変換として導来局所化へ降ろす。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open DifferentialGraded HomologicalComplex CochainComplex HomComplex

variable {R : Type u} [CommRing R]

/-- 概要：単位パラメータから通常鎖写像への変換は後合成を保つ。
方針：零次数 cochain へ写し、単位 cycle の後合成公式を使う。
規約：KST §3.1。使われ方：指定加群比較の成分の自然性。 -/
theorem mapFromUnit_postcompose {X Y Z : Complex R}
    (a : 𝟙_ (Complex R) ⟶ homComplex R X Y) (f : Y ⟶ Z) :
    mapFromUnit R X Z (a ≫ homPostcompose X f) = mapFromUnit R X Y a ≫ f := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp]
  rw [complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
  change (cycleFromUnit (homComplex R X Z) (a ≫ homPostcompose X f)).val =
    (cycleFromUnit (homComplex R X Y) a).val.comp (Cochain.ofHom f) (zero_add (0 : ℤ))
  rw [cycleFromUnit_postcomp]
  rfl

/-- 概要：単位パラメータから通常鎖写像への変換は前合成を保つ。
方針：零次数 cochain と単位 cycle の後合成公式を使う。
規約：KST §3.1。使われ方：指定加群比較の成分の自然性。 -/
theorem mapFromUnit_precompose {X Y Z : Complex R}
    (f : X ⟶ Y) (a : 𝟙_ (Complex R) ⟶ homComplex R Y Z) :
    mapFromUnit R X Z (a ≫ homPrecompose f Z) = f ≫ mapFromUnit R Y Z a := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp]
  rw [complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
  change (cycleFromUnit (homComplex R X Z) (a ≫ homPrecompose f Z)).val =
    (Cochain.ofHom f).comp (cycleFromUnit (homComplex R Y Z) a).val (zero_add (0 : ℤ))
  rw [cycleFromUnit_postcomp]
  rfl

variable {C : Type v} {D : Type w} [DGCategory R C] [DGCategory R D]
  [Small.{u} C] [Small.{u} D]

omit [Small.{u} C] in
/-- 概要：指定比較の各成分は入力図式加群の射について自然。
方針：加群射の全次数自然性を指定単位矢に前合成して通常鎖写像へ戻す。
規約：KST §3.1。使われ方：比較を加群評価関手間の自然変換にする。 -/
theorem transitionModuleComponent_natural {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    {M N : ModuleCategory R Dᵒᵖ} (f : M ⟶ N) (x : C) :
    (moduleEvaluation R Dᵒᵖ (op (F.obj x))).map f ≫
        transitionModuleComponent τ (ForgetEnrichment.to (Complex R) N) x =
      transitionModuleComponent τ (ForgetEnrichment.to (Complex R) M) x ≫
        (moduleEvaluation R Dᵒᵖ (op (G.obj x))).map f := by
  have h := closedTransApp_naturality R (moduleClosedHomEquiv R Dᵒᵖ M N f)
    (op (op (F.obj x))) (op (op (G.obj x)))
  rw [moduleClosedHomEquiv_app, moduleClosedHomEquiv_app] at h
  have hh := congrArg (fun s => τ.app x ≫ s) h
  have hm := congrArg (fun s => mapFromUnit R
    ((ForgetEnrichment.to (Complex R) M).obj (op (op (F.obj x))))
    ((ForgetEnrichment.to (Complex R) N).obj (op (op (G.obj x)))) s) hh
  simpa only [← Category.assoc, mapFromUnit_postcompose, mapFromUnit_precompose,
    transitionModuleComponent] using hm.symm

/-- 概要：指定単位矢から得た dg 加群射は入力加群について自然。
方針：主 Hom end の射を各評価で比較し、成分の自然性へ帰着する。
規約：KST §3.1。使われ方：局所加群比較の自然変換の自然性フィールド。 -/
theorem transitionModuleMorphism_natural {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G)
    {M N : ModuleCategory R Dᵒᵖ} (f : M ⟶ N) :
    (moduleRestriction R Cᵒᵖ Dᵒᵖ F.op.op).map f ≫
        transitionModuleMorphism τ (ForgetEnrichment.to (Complex R) N) =
      transitionModuleMorphism τ (ForgetEnrichment.to (Complex R) M) ≫
        (moduleRestriction R Cᵒᵖ Dᵒᵖ G.op.op).map f := by
  apply moduleMorphism_ext
  intro x
  change (moduleEvaluation R Cᵒᵖ (op x.unop)).map
      ((moduleRestriction R Cᵒᵖ Dᵒᵖ F.op.op).map f ≫
        transitionModuleMorphism τ (ForgetEnrichment.to (Complex R) N)) =
    (moduleEvaluation R Cᵒᵖ (op x.unop)).map
      (transitionModuleMorphism τ (ForgetEnrichment.to (Complex R) M) ≫
        (moduleRestriction R Cᵒᵖ Dᵒᵖ G.op.op).map f)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    transitionModuleMorphism_eval, transitionModuleMorphism_eval,
    moduleRestriction_map_eval, moduleRestriction_map_eval]
  exact transitionModuleComponent_natural τ f x.unop

/-- 概要：指定の全次数自然変換は局所加群制限関手間の実際の自然変換を誘導する。
方針：構成済みの各加群上の射と自然性を束ねる。
規約：KST §3.1。使われ方：canonical な比較の導来自然変換への持ち上げ。 -/
def transitionModuleNatTrans {F G : DGFunctor R C D}
    (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R))) F G) :
    moduleRestriction R Cᵒᵖ Dᵒᵖ F.op.op ⟶ moduleRestriction R Cᵒᵖ Dᵒᵖ G.op.op where
  app M := transitionModuleMorphism τ (ForgetEnrichment.to (Complex R) M)
  naturality _ _ f := transitionModuleMorphism_natural τ f

end SerrePositivity.KST.DerivedBlowup
