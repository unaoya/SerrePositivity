module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomSourceNaturality
public import SerrePositivity.HomologicalAlgebra.LinearWeightEndTotalParameters
public import SerrePositivity.EInfinity.PowerOperation.LinearHomComplexFunctor

/-!
概要：指定符号付きend–Hom同型は係数図式の射の後合成と可換。
方針：元の積射影と零延長の指定行同型で全成分を照合する。
規約：IS-W2 D01の既存構成の自然性則。計算上限を変えない。
使われ方：HA 1.2.4、同じBK錐の全図式射への自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable (K : ChainComplex (Jᵒᵖ ⥤ ModuleCat A) ℕ)

/-- 零延長の指定行は同じ係数複体の後合成と可換。 -/
theorem extendedChainHomRows_postcomp {H H' : CochainComplex (Jᵒᵖ ⥤ ModuleCat A) ℤ}
    (f : H ⟶ H') (q : ℤ) (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q)
    (n : ℕ) :
    extendedChainHomRows K H' q ((intervalHomPrePost A (𝟙 _) f).f q z) n =
      extendedChainHomRows K H q z n ≫ f.f (q-n) := by
  change (negativeChainRowIso K n).inv ≫
    ((Cochain.ofHom (𝟙 _)).comp
      (z.comp (Cochain.ofHom f) (add_zero q)) (zero_add q)).v (-n) (q-n) (by omega) = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.id_comp]
  exact (Category.assoc _ _ _).symm

/-- 同じend–Hom同型は元の係数図式の全射に厳密に自然。 -/
theorem weightEndHomIso_target_naturality {X Y : Jᵒᵖ ⥤ Complex A} (f : X ⟶ Y) :
    (linearWeightEndTotalMap A f).app (op K) ≫ (weightEndHomIso A K Y).hom =
      (weightEndHomIso A K X).hom ≫
        intervalHomPrePost A (𝟙 (K.extend ComplexShape.embeddingDownNat))
          ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (extendedChainHomRowsLinearEquiv K
    ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).obj Y) A q).injective
  funext n
  change extendedChainHomRows K _ q
      (weightEndHomComponentsEquiv A K Y q ((linearWeightEndTotalMap A f).app (op K) |>.f q <| z)) n =
    extendedChainHomRows K _ q
      ((intervalHomPrePost A (𝟙 _)
        ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f)).f q
          (weightEndHomComponentsEquiv A K X q z)) n
  rw [weightEndHomComponentsEquiv_rows, extendedChainHomRows_postcomp,
    weightEndHomComponentsEquiv_rows]
  have h := congrArg (fun g => g z) (CochainProductTotal.componentπ_naturality
    ((linearWeightEndCochainMap A f).app (op K)) n q)
  change CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A Y).obj (op K)) n q
      (((linearWeightEndTotalMap A f).app (op K)).f q z) =
    CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A X).obj (op K)) n q z ≫
        ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f).f (q-n) at h
  rw [h]
  exact (Linear.units_smul_comp _ _ _).symm

/-- 係数後合成の同じ法則を既存の線形Hom全関手で読む。 -/
theorem weightEndHomIso_target_naturality_postcompose {X Y : Jᵒᵖ ⥤ Complex A}
    (f : X ⟶ Y) :
    (linearWeightEndTotalMap A f).app (op K) ≫ (weightEndHomIso A K Y).hom =
      (weightEndHomIso A K X).hom ≫
        SerrePositivity.EInfinity.PowerOperation.linearHomComplexPostcompose A
          (K.extend ComplexShape.embeddingDownNat)
          ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f) := by
  rw [weightEndHomIso_target_naturality]
  congr 1
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let b := (functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).map f
  change (Cochain.ofHom (𝟙 (K.extend ComplexShape.embeddingDownNat))).comp
    (z.comp (Cochain.ofHom b) (add_zero q)) (zero_add q) =
      z.comp (Cochain.ofHom b) (add_zero q)
  exact Cochain.id_comp (z.comp (Cochain.ofHom b) (add_zero q))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
