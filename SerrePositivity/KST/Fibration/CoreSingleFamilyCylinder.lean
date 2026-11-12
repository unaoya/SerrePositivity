module
public import SerrePositivity.KST.Fibration.CoreFamilyDiagonalCylinder
public import SerrePositivity.KST.Fibration.QuotientSKernelNullCoreAction
public import SerrePositivity.KST.Fibration.CoreSingleCoordinates

/-!
概要：元の商核円柱を、一回の全豊穣実現族の同じ対角評価として回収する。
方針：恒等成分の図式同型の対角を元の実現同型と照合し、全評価を輸送する。
規約：円柱の全パラメータと元の包含・商の実合成を保持する。
使われ方：商実現四角形と指定 Verdier 二胞体との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 一回の全 native 図式から元の core S• への、恒等成分を持つ同じ座標同型。 -/
def coreSingleSimplicialIso (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableMultiSCoreObjectEnrichedFunctor 1).obj A).diagram ≅
      simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- 同じ図式座標同型の対角は、元の単回実現座標同型の逆射そのもの。 -/
theorem coreSingleSimplicialIso_diagonal_hom (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    simplicialDiagonalFunctor.map (coreSingleSimplicialIso A).hom =
      (coreSingleRealizationIso (stableCategoryModel A)).inv := by
  apply NatTrans.ext
  funext n
  rfl

/-- 逆向きの図式座標の対角も、元の単回実現座標同型の順射と一致する。 -/
theorem coreSingleSimplicialIso_diagonal_inv (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    simplicialDiagonalFunctor.map (coreSingleSimplicialIso A).inv =
      (coreSingleRealizationIso (stableCategoryModel A)).hom := by
  apply NatTrans.ext
  funext n
  rfl

/-- 同じ全入力族の各段を回収する元の円柱は、同じ native 全図式円柱に等しい。 -/
theorem singleCoreFamilyCylinder_coordinates {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (K : (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⋙ tensorRight P ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor)
    (hK : ∀ n, K.app n =
      uncurry (H ≫ ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C)) :
    CategoryTheory.Functor.whiskerRight (coreSingleSimplicialIso A).hom (tensorRight P) ≫ K =
      stableMultiCoreFamilyCylinder 1 H ≫ (coreSingleSimplicialIso C).hom := by
  apply NatTrans.ext
  funext n
  change (𝟙 _ ▷ P) ≫ K.app n = (stableMultiCoreFamilyCylinder 1 H).app n ≫ 𝟙 _
  rw [id_whiskerRight, Category.id_comp, Category.comp_id]
  exact (hK n).trans (stableMultiCoreFamilyCylinder_app 1 H n).symm

/-- 同じ元の円柱の対角は、同じ全豊穣実現族の評価を座標同型で厳密に回収する。 -/
theorem singleCoreFamilyCylinder_diagonal {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (K : (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⋙ tensorRight P ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor)
    (hK : ∀ n, K.app n =
      uncurry (H ≫ ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C)) :
    (simplicialDiagonalFunctor.map (coreSingleSimplicialIso A).hom ▷ P) ≫
        simplicialCylinderDiagonal _ _ P K =
      uncurry (H ≫ (stableMultiRealizationEnrichedFunctor 1).map A C) ≫
        simplicialDiagonalFunctor.map (coreSingleSimplicialIso C).hom := by
  have he := singleCoreFamilyCylinder_coordinates H K hK
  have hd := congrArg (fun t => simplicialCylinderDiagonal _ _ P t) he
  rw [simplicialCylinderDiagonal_precomp, simplicialCylinderDiagonal_postcomp,
    stableMultiCoreFamilyCylinder_diagonal] at hd
  exact hd

/-- 商核から来る元の零化円柱は、同じ実合成の全豊穣実現族の評価そのもの。 -/
theorem quotientSKernelNullCylinder_native
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    (simplicialDiagonalFunctor.map (coreSingleSimplicialIso A).hom ▷ (Δ[1] : SSet.{u})) ≫
        quotientSKernelNullCylinder h =
      uncurry (zeroEndPostcompFamily
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) ≫
            (stableMultiRealizationEnrichedFunctor 1).map
              (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) ≫
        simplicialDiagonalFunctor.map (coreSingleSimplicialIso C).hom := by
  have he := singleCoreFamilyCylinder_diagonal _ (quotientSKernelNullNatTrans h)
    (quotientSKernelNullNatTrans_app h)
  rw [quotientSKernelNullNatTrans_diagonal] at he
  exact he

/-- 元の core S 対象で読んだ商核円柱は、同じ全 Hom 評価の座標輸送である。 -/
theorem quotientSKernelNullCylinder_realization
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    quotientSKernelNullCylinder h =
      ((coreSingleRealizationIso (stableCategoryModel (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))).hom ▷
          (Δ[1] : SSet.{u})) ≫
        uncurry (zeroEndPostcompFamily
          (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
            (verdierSequenceComposite_zero h) ≫
              (stableMultiRealizationEnrichedFunctor 1).map
                (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A) (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) ≫
          (coreSingleRealizationIso (stableCategoryModel (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))).inv := by
  have he := quotientSKernelNullCylinder_native h
  rw [coreSingleSimplicialIso_diagonal_hom, coreSingleSimplicialIso_diagonal_hom] at he
  rw [← he, ← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp]

end SerrePositivity.KST.Fibration
