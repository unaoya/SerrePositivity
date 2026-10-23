module
public import SerrePositivity.KST.Fibration.CoreFamilyDiagonalCylinder
public import SerrePositivity.KST.Fibration.QuotientSKernelNullCoreAction

/-! # 元の商核円柱を、一回の全豊穣実現族の同じ対角評価として回収する -/

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
def coreSingleSimplicialIso (A : StableQCat.{u}) :
    ((stableMultiSCoreObjectEnrichedFunctor 1).obj A).diagram ≅
      simplicialSConstruction A.obj ⋙ quasicategoryCoreFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- 同じ全入力族の各段を回収する元の円柱は、同じ native 全図式円柱に等しい。 -/
theorem singleCoreFamilyCylinder_coordinates {A C : StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (K : (simplicialSConstruction A.obj ⋙ quasicategoryCoreFunctor) ⋙ tensorRight P ⟶
      simplicialSConstruction C.obj ⋙ quasicategoryCoreFunctor)
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
theorem singleCoreFamilyCylinder_diagonal {A C : StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (K : (simplicialSConstruction A.obj ⋙ quasicategoryCoreFunctor) ⋙ tensorRight P ⟶
      simplicialSConstruction C.obj ⋙ quasicategoryCoreFunctor)
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
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) :
    (simplicialDiagonalFunctor.map (coreSingleSimplicialIso A).hom ▷ (Δ[1] : SSet.{u})) ≫
        quotientSKernelNullCylinder h =
      uncurry (zeroEndPostcompFamily
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) ≫
            (stableMultiRealizationEnrichedFunctor 1).map
              (show StableQCat from A) (show StableQCat from C)) ≫
        simplicialDiagonalFunctor.map (coreSingleSimplicialIso C).hom := by
  have he := singleCoreFamilyCylinder_diagonal _ (quotientSKernelNullNatTrans h)
    (quotientSKernelNullNatTrans_app h)
  rw [quotientSKernelNullNatTrans_diagonal] at he
  exact he

end SerrePositivity.KST.Fibration
