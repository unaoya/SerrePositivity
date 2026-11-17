module

public import SerrePositivity.AlgebraicGeometry.ComplexValuedAugmentedDouble
public import SerrePositivity.AlgebraicGeometry.CechTripleTotalDifferential

/-!
概要：複体値の増大二重Čech図式で、二つの増大軸の完全性を比較する。
方針：二方向の交換、三重totalの結合、および既存の零次列の擬同型を使う。
規約：元の全ての増大点を含め、整数係数の符号付きtotalを保持する。
使われ方：相対fppfの二変数の比較（承認済み計画C07・C11）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false
attribute [local instance] cechIntegerTotalShapeSymmetry

/-- 二つの増大方向の交換を、元の三重totalの同型へ送る。 -/
def complexValuedAugmentedDouble_swapIso
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ) :
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ)
        (complexValuedAugmentedDouble F) up) up ≅
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ)
        (complexValuedAugmentedDouble ((Prod.braiding _ _).functor ⋙ F)) up) up := by
  let K := complexValuedAugmentedDouble F
  let G := (Prod.braiding _ _).functor ⋙ F
  let E := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
    (Functor.curryObj F ⋙
      AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor ⋙
        SerrePositivity.Cech.augmentedCochain)
  let e (i : ℕ) : K.flip.X i ≅ (complexValuedAugmentedDouble G).X i := by
    cases i <;> exact SerrePositivity.Cech.mapAugmentedCochainIso
      (HomologicalComplex.eval (CochainComplex (ModuleCat.{u} ℤ) ℕ) up _) E
  let eK : K.flip ≅ complexValuedAugmentedDouble G :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j hij
      have h : i+1=j := hij
      subst j
      apply HomologicalComplex.Hom.ext
      funext m
      cases i <;> cases m
      all_goals
        change (𝟙 _) ≫ _ = _ ≫ (𝟙 _)
        rw [Category.id_comp, Category.comp_id]
      all_goals first | rfl | skip
      case succ.zero n =>
        let H := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
          (Functor.curryObj G ⋙
            AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor ⋙
              SerrePositivity.Cech.augmentedCochain)
        change ((SerrePositivity.Cech.augmentedCochain.obj H).d (n+1) (n+1+1)).f 0 =
          (SerrePositivity.Cech.augmentedCochain.obj
            (SerrePositivity.Cech.col F 0)).d (n+1) (n+1+1)
        rw [SerrePositivity.Cech.augmentedCochain_d,
          SerrePositivity.Cech.augmentedCochain_d]
        change (∑ i : Fin (n+2), (-1 : ℤ)^i.val • H.right.δ i).f 0 =
          ∑ i : Fin (n+2), (-1 : ℤ)^i.val • (H.right.δ i).f 0
        exact (map_sum (HomologicalComplex.Hom.fAddMonoidHom
          (C₁ := H.right.obj (SimplexCategory.mk n))
          (C₂ := H.right.obj (SimplexCategory.mk (n+1))) 0)
          (fun i : Fin (n+2) ↦ (-1 : ℤ)^i.val • H.right.δ i) Finset.univ).trans
          (by simp only [map_zsmul]; rfl)
      case succ.succ n m =>
        let H := AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor.obj
          (Functor.curryObj G ⋙
            AugmentedSimplexCategory.equivAugmentedCosimplicialObject.functor ⋙
              SerrePositivity.Cech.augmentedCochain)
        change ((SerrePositivity.Cech.augmentedCochain.obj H).d (n+1) (n+1+1)).f (m+1) =
          (SerrePositivity.Cech.augmentedCochain.obj
            (SerrePositivity.Cech.col F (m+1))).d (n+1) (n+1+1)
        rw [SerrePositivity.Cech.augmentedCochain_d,
          SerrePositivity.Cech.augmentedCochain_d]
        change (∑ i : Fin (n+2), (-1 : ℤ)^i.val • H.right.δ i).f (m+1) =
          ∑ i : Fin (n+2), (-1 : ℤ)^i.val • (H.right.δ i).f (m+1)
        exact (map_sum (HomologicalComplex.Hom.fAddMonoidHom
          (C₁ := H.right.obj (SimplexCategory.mk n))
          (C₂ := H.right.obj (SimplexCategory.mk (n+1))) (m+1))
          (fun i : Fin (n+2) ↦ (-1 : ℤ)^i.val • H.right.δ i) Finset.univ).trans
          (by simp only [map_zsmul]; rfl))
  exact HomologicalComplex₂.total.mapIso
    ((HomologicalComplex₂.totalFlipIso K up).symm ≪≫
      HomologicalComplex₂.total.mapIso eK up) up

/-- 正の列・行の増大totalが完全なら、二つの零次軸の増大totalの完全性は同値。 -/
theorem complexValuedDoubleCech_axes_acyclic_iff
    (F : AugmentedSimplexCategory × AugmentedSimplexCategory ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ)
    (hc : ∀ i, 0 < i → (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col F i)) up).Acyclic)
    (hr : ∀ j, 0 < j → (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.row F j)) up).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col F 0)) up).Acyclic ↔
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.row F 0)) up).Acyclic := by
  let G := (Prod.braiding _ _).functor ⋙ F
  have hrow (i : ℕ) : SerrePositivity.Cech.col G i = SerrePositivity.Cech.row F i := rfl
  haveI hqF := complexValuedAugmentedDouble_columnZeroProjection_quasiIso F hc
  haveI hqG := complexValuedAugmentedDouble_columnZeroProjection_quasiIso G
    (fun i hi ↦ by rw [hrow]; exact hr i hi)
  let e := (cechTripleTotalAssociator (complexValuedAugmentedDouble F)).symm ≪≫
    complexValuedAugmentedDouble_swapIso F ≪≫
      cechTripleTotalAssociator (complexValuedAugmentedDouble G)
  change _ ↔ (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
    (SerrePositivity.Cech.augmentedCochain.obj (SerrePositivity.Cech.col G 0)) up).Acyclic
  constructor
  · intro h n
    have ht := (exactAt_iff_of_quasiIsoAt
      (complexValuedAugmentedDouble_columnZeroProjection F) n).mpr (h n)
    exact (exactAt_iff_of_quasiIsoAt
      (complexValuedAugmentedDouble_columnZeroProjection G) n).mp (ht.of_iso e)
  · intro h n
    have ht := (exactAt_iff_of_quasiIsoAt
      (complexValuedAugmentedDouble_columnZeroProjection G) n).mpr (h n)
    exact (exactAt_iff_of_quasiIsoAt
      (complexValuedAugmentedDouble_columnZeroProjection F) n).mp (ht.of_iso e.symm)

end SerrePositivity.AlgebraicGeometry
