module
public import SerrePositivity.HomologicalAlgebra.WeightEndHomIso
public import SerrePositivity.HomologicalAlgebra.WeightEndHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.HomotopyIntervalNaturality
/-!
概要：指定符号付きend–Hom同型は重みの鎖射の前合成と可換。
方針：元の積射影と零延長の指定行同型で全成分を照合する。
規約：IS-W2 B02の前提計算1/3、既存の構成の自然性。計算上限は変えない。
使われ方：HA 1.2.4、指定Moore反転のend移送と元の錐代表の前合成の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]
variable {K L : ChainComplex (Jᵒᵖ ⥤ ModuleCat A) ℕ}
/-- 零延長した同じ前合成の元の鎖次数での値。 -/
theorem extendedChainHomRows_precomp (f : K ⟶ L)
    (H : CochainComplex (Jᵒᵖ ⥤ ModuleCat A) ℤ) (q : ℤ)
    (z : Cochain (L.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows K H q
      ((intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
        (𝟙 H)).f q z) n = f.f n ≫ extendedChainHomRows L H q z n := by
  change (negativeChainRowIso K n).inv ≫
    ((Cochain.ofHom (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)).comp
      (z.comp (Cochain.ofHom (𝟙 H)) (add_zero q)) (zero_add q)).v (-n) (q-n) (by omega) = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id]
  rw [HomologicalComplex.extendMap_f f ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl]
  simp only [negativeChainRowIso, extendedChainHomRows, Category.assoc,
    Iso.inv_hom_id_assoc]
/-- 指定end–Hom同型は同じ重みの鎖射による前合成と厳密に可換。 -/
theorem weightEndHomIso_source_naturality (f : K ⟶ L) (X : Jᵒᵖ ⥤ Complex A) :
    (linearWeightEndTotalFunctor A X).map f.op ≫ (weightEndHomIso A K X).hom =
      (weightEndHomIso A L X).hom ≫
        intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
          (𝟙 ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).obj X)) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (extendedChainHomRowsLinearEquiv K
    ((functorToComplexOfFunctors Jᵒᵖ (ModuleCat A) (.up ℤ)).obj X) A q).injective
  funext n
  change extendedChainHomRows K _ q
      (weightEndHomComponentsEquiv A K X q ((linearWeightEndTotalFunctor A X).map f.op |>.f q <| z)) n =
    extendedChainHomRows K _ q
      ((intervalHomPrePost A (HomologicalComplex.extendMap f ComplexShape.embeddingDownNat)
        (𝟙 _)).f q (weightEndHomComponentsEquiv A L X q z)) n
  rw [weightEndHomComponentsEquiv_rows, extendedChainHomRows_precomp,
    weightEndHomComponentsEquiv_rows]
  have h := congrArg (fun g => g z) (CochainProductTotal.componentπ_naturality
    ((linearWeightEndCochainFunctor A X).map f.op) n q)
  change CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A X).obj (op K)) n q
      (((linearWeightEndTotalFunctor A X).map f.op).f q z) =
    f.f n ≫ CochainProductTotal.componentπ
      ((linearWeightEndCochainFunctor A X).obj (op L)) n q z at h
  rw [h]
  exact (Linear.comp_units_smul _ _ _).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
