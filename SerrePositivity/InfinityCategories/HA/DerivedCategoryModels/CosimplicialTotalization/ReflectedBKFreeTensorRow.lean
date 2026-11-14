module
public import SerrePositivity.HomologicalAlgebra.CochainOfHomPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomIsoEvaluation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSourceComposition
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKSourceEvaluation

/-!
概要：A12の実始域射を通した自由重み成分は、元の錐代表との実dg合成を与える。
方針：指定自由重みの行評価とBK行の始域自然性を合成しtensor符号を消す。
規約：全斉次射・全重み次数を保持する既存構成の評価・合成則。
使われ方：HA 1.2.4、IS-W2 B02の各AW切断条件を閉じる成分計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {A : Type u} [CommRing A]
local notation "E" => functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (ComplexShape.up ℤ)
local notation "V" => Functor.flip (Functor.obj SimplicialObject.opFunctor bousfieldKanSetWeight)
local notation "U" => freeLinearizedSimplicialWeight A (Functor.flip V)

/-- 同じ実A12始域射の自由重み成分でもtensor符号が消え、実錐代表との合成になる。 -/
theorem reflectedBKFreeHom_tensor_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let η := (Cochain.ofHom σ).comp
      (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) (p - n) (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        (((η.v (-(n : ℤ)) (0 - n) (by omega)).app j) w) f (by omega) := by
  dsimp only
  let L := (normalizedMooreComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat A)).obj U
  let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
    extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
      ComplexShape.embeddingDownNat
  let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
  let η := (Cochain.ofHom σ).comp
    (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)
  let e := freeLinearWeightDiagramIso A V
  let x' := ((negativeChainRowIso L n).hom.app j) (((e.inv.f (-(n : ℤ))).app j) w)
  have h := homToNormalizedBousfieldKan_tensor_source_row L
    (e.hom ≫ σ) P X p f n j x'
  dsimp only at h
  have hχ := ConcreteCategory.congr_hom
    (NatTrans.congr_app (extendedChainHomRows_iso_evaluation L _ _ e p χ n) j) w
  have hη := ConcreteCategory.congr_hom
    (NatTrans.congr_app (extendedChainHomRows_iso_evaluation L _ _ e 0 η n) j) w
  simp only [NatTrans.comp_app, ModuleCat.comp_apply] at hχ hη
  dsimp only [χ, η] at hχ hη
  rw [zeroSourcePrecomp_comp] at hχ hη

  have hc := congrArg (fun t : Homogeneous P ((doubleOppositeDiagram X).obj j) (p - n) =>
    ((-(n : ℤ)) * p).negOnePow • t) hχ
  have he := congrArg (fun t : Homogeneous ((productTotalFunctor A).obj X)
      ((doubleOppositeDiagram X).obj j) (0 - n) =>
    compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
      (x := P) (y := (productTotalFunctor A).obj X)
      (z := (doubleOppositeDiagram X).obj j) t f (by omega)) hη
  exact hc.symm.trans (h.trans he)

/-- 元の錐代表の実複体射で右辺を表し、AWの任意の全次数へ合わせた成分式。 -/
theorem reflectedBKFreeHom_tensor_component (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) (p - n) (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w)
        f (by omega) := by
  dsimp only
  let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
    extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
      ComplexShape.embeddingDownNat
  have hg : HEq
      (((((Cochain.ofHom σ).comp (Cochain.ofHom
        (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)).v
          (-(n : ℤ)) (0 - n) (by omega)).app j) w)
      ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w) := by
    exact cochainOfHom_comp_v_app_heq σ (normalizedBousfieldKanConeRepresentative X)
      (-(n : ℤ)) (0 - n) (by omega) j w

  have h := reflectedBKFreeHom_tensor_row P X p f n j w
  dsimp only at h
  refine h.trans ?_
  exact AWAssocTerms.compose_eq_of_heq (R := A) (D := Complex A)
    (x := P) (y := (productTotalFunctor A).obj X)
    (z := (doubleOppositeDiagram X).obj j)
    (p := p) (p' := p) (q := 0 - (n : ℤ)) (q' := -(n : ℤ)) (k := p - n)
    _ _ f f hg (HEq.rfl) rfl (by omega) (by omega) (by omega)

/-- 同じ成分式の終次数をAWの指定全次数へ合わせる。 -/
theorem reflectedBKFreeHom_tensor_component_of_degree (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ) (n : ℕ) (r : ℤ) (hr : p - n = r)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p)
    (j : SimplexCategoryᵒᵖᵒᵖ)
    (w : (((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (V ⋙ SSet.uliftFunctor.{u,0}))).X (-(n : ℤ))).obj j) :
    let σ := (normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat
    let χ := (Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)
    ((-(n : ℤ)) * p).negOnePow • ((χ.v (-(n : ℤ)) r (by omega)).app j) w =
      compose A (D := Complex A) (p := p) (q := -(n : ℤ)) (n := r)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j)
        ((((σ ≫ normalizedBousfieldKanConeRepresentative X).f (-(n : ℤ))).app j) w)
        f (by omega) := by
  subst r
  exact reflectedBKFreeHom_tensor_component P X p n f j w

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
