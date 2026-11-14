module
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomSourceMap
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKTensorRow

/-!
概要：指定BK行の合成則を任意の同じ重みの始域射による前合成へ運ぶ。
方針：行表示の始域自然性と元のBK行の合成・tensor符号消去則を使う。
規約：元の錐代表と全次数を保持する既存構成の自然性・合成則。
使われ方：HA 1.2.4、IS-W2 B02の係数重み比較とMoore反転を通す各切断の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable {A : Type u} [CommRing A]
local notation "E" => functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (ComplexShape.up ℤ)
variable (L : ChainComplex (SimplexCategoryᵒᵖᵒᵖ ⥤ ModuleCat A) ℕ)
variable (σ : L.extend ComplexShape.embeddingDownNat ⟶
  normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat)

/-- 始域射を前合成したBK行も、同じ前合成した錐代表との合成則を満たす。 -/
theorem homToNormalizedBousfieldKan_rows_source_cone (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ) :
    extendedChainHomRows L ((E).obj (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)) n =
      ((n : ℤ) * p).negOnePow •
        (extendedChainHomRows L
          ((E).obj (doubleOppositeDiagram
            ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) 0
          ((Cochain.ofHom σ).comp
            (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)) n ≫
          homDiagramDegreePrecompose X p (0 - n) (p - n) (by omega) f) := by
  rw [extendedChainHomRows_precomp, homToNormalizedBousfieldKan_rows_cone,
    extendedChainHomRows_precomp]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Category.assoc]

/-- 同じ始域射で移した行でもtensor符号が消え、元の実dg合成となる。 -/
theorem homToNormalizedBousfieldKan_tensor_source_row (P : Complex A)
    (X : CosimplicialObject (Complex A)) (p : ℤ)
    (f : Homogeneous P ((productTotalFunctor A).obj X) p) (n : ℕ)
    (j : SimplexCategoryᵒᵖᵒᵖ) (x : (L.X n).obj j) :
    let η := extendedChainHomRows L
      ((E).obj (doubleOppositeDiagram
        ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X))) 0
      ((Cochain.ofHom σ).comp
        (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) (zero_add 0)) n
    let χ := extendedChainHomRows L
      ((E).obj (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) p
      ((Cochain.ofHom σ).comp ((homToNormalizedBousfieldKan P X).f p f) (zero_add p)) n
    ((-(n : ℤ)) * p).negOnePow • χ.app j x =
      compose A (D := Complex A) (p := p) (q := 0 - n) (n := p - n)
        (x := P) (y := (productTotalFunctor A).obj X)
        (z := (doubleOppositeDiagram X).obj j) (η.app j x) f (by omega) := by
  dsimp only
  rw [extendedChainHomRows_precomp, extendedChainHomRows_precomp]
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  exact homToNormalizedBousfieldKan_tensor_row P X p f n j
    (((negativeChainRowIso normalizedBousfieldKanWeight n).hom.app j)
      ((σ.f (-(n : ℤ))).app j (((negativeChainRowIso L n).inv.app j) x)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
