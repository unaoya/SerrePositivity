module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeComposition
public import SerrePositivity.DifferentialGraded.Category.Basic

/-!
# 指定 BK 行の tensor–Hom 符号と実 dg 合成

概要：指定BK行にtensor–HomのKoszul符号を掛けると元の錐代表との実dg合成になる。
方針：行の合成則と既存の複体の豊穣合成の成分式で二つの符号を消す。
規約：IS-W2 B02の同じ全パラメータ成分照合の分割。
使われ方：HA 1.2.4、AWの各切断での自由鎖比較と実標準合成の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped TensorProduct
variable {A : Type u} [CommRing A]

/-- 概要：tensor逆転置の符号と指定BK行の符号が消え、実dg合成となる。
方針：同じ錐代表の行と元のenrichedCompositionの成分式。
規約：任意の試験cochain・重みの元。使われ方：HA 1.2.4 のAW各切断の照合。 -/
theorem homToNormalizedBousfieldKan_tensor_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ) (x : ((normalizedBousfieldKanWeight (A := A)).X n).obj j) :
    let η := extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
      0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n
    let χ := extendedChainHomRows normalizedBousfieldKanWeight
      ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((homToNormalizedBousfieldKan P X).f p f) n
    ((-(n : ℤ)) * p).negOnePow • χ.app j x =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j) (η.app j x) f (by omega) := by
  dsimp only
  let z := (extendedChainHomRows normalizedBousfieldKanWeight
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)))
    0 (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) n).app j x
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (homToNormalizedBousfieldKan_rows_cone P X p f n) j) x
  change (extendedChainHomRows normalizedBousfieldKanWeight
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
    ((homToNormalizedBousfieldKan P X).f p f) n).app j x =
      ((n : ℤ) * p).negOnePow • f.comp z (n₁₂ := p - n) (by omega) at h
  have hc : compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
      (x := P) (y := (productTotalFunctor A).obj X)
      (z := (doubleOppositeDiagram X).obj j) z f (by omega) =
      f.comp z (n₁₂ := p - n) (by omega) := by
    change (p * (0 - (n : ℤ))).negOnePow •
      (enrichedComposition P ((productTotalFunctor A).obj X)
        ((doubleOppositeDiagram X).obj j)).f (p - n)
        (ιTensorObj (homComplex A P ((productTotalFunctor A).obj X))
          (homComplex A ((productTotalFunctor A).obj X) ((doubleOppositeDiagram X).obj j))
          p (0 - n) (p - n) (by omega) (f ⊗ₜ[A] z)) = _
    rw [enrichedComposition_apply, smul_smul, Int.units_mul_self, one_smul]
  rw [hc, h, smul_smul]
  have hs : ((-(n : ℤ)) * p).negOnePow * ((n : ℤ) * p).negOnePow = 1 := by
    rw [← Int.negOnePow_add]
    have he : (-(n : ℤ)) * p + (n : ℤ) * p = 0 := by ring
    rw [he]
    rfl
  rw [hs, one_smul]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
