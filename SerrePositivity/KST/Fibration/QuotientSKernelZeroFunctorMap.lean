module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSDiagramFamily
public import SerrePositivity.KST.Fibration.QuotientSKernelContractionFullS

/-!
概要：元の商核上辺を、同じ零値完全関手による全 S• 作用へ厳密に接続する。
方針：元の全 S_n 包含と実商射影の等式を core の単射性で反映する。
規約：指定した包含・商と全相対図式を保持し、零射を選び直さない。
使われ方：元の商核四角形と指定 Verdier 上側二胞体の全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 元の商核上辺は、全相対核包含後の同じ零値完全関手の全 S• 作用である。 -/
theorem quotientSKernelTop_zeroFunctorFullSMap (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q =
      (relativeSKernelSimplicialIso h).hom ≫
        zeroFunctorFullSMap (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) := by
  apply NatTrans.ext
  funext n
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι).1
  change (relativeSFunctorMap i q.hom n.unop.len ≫ relativeSQuotientMap q n.unop.len) ≫ _ =
    ((relativeSKernelTopIso h n.unop.len).hom ≫ zeroFunctorSCoreMap
      (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
      (verdierSequenceComposite_zero h) n.unop.len) ≫ _
  simp only [Category.assoc]
  rw [zeroFunctorSCoreMap_ι]
  exact (Category.assoc _ _ _).symm.trans (quotientSKernelTop_fullS h n.unop.len)

/-- 元の全核円柱を読む同じ零値関手パラメータ。 -/
def quotientSKernelZeroFunctorParameter (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    (Δ[1] : SSet.{u}) ⟶ zeroFunctorLocus A C :=
  zeroStableHomFamilyLift
    (zeroEndPostcompFamily (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
      (verdierSequenceComposite_zero h))
    (zeroEndPostcompFamily_zero_vertices _ _)

/-- 完全関手空間で、元の円柱の同じ全単体を回収する。 -/
theorem quotientSKernelZeroFunctorParameter_toExact (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    quotientSKernelZeroFunctorParameter h ≫ zeroFunctorLocusToExact A C =
      zeroEndPostcompFamily
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι := by
  have he := congrArg (fun f => f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι)
    (zeroStableHomFamilyLift_recovery
      (zeroEndPostcompFamily
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
          (verdierSequenceComposite_zero h))
      (zeroEndPostcompFamily_zero_vertices _ _))
  rw [Category.assoc, zeroFunctorLocusToStableHom_inclusion] at he
  exact he

/-- 元の相対核円柱は、全 S• の豊穣 Hom 族の同じ全パラメータ評価。 -/
theorem quotientSKernelContractionImage_diagramFamily (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (n : SimplexCategoryᵒᵖ) :
    (quotientSKernelContractionImage h).app n =
      ((relativeSKernelTopIso h n.unop.len).hom ▷ (Δ[1] : SSet.{u})) ≫
        (diagramFamilyCylinder _ _ (Δ[1] : SSet.{u})
          (quotientSKernelZeroFunctorParameter h ≫ zeroFunctorFullSDiagramFamily A C)).app n := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι).1
  rw [quotientSKernelContractionImage_fullS]
  change _ = ((_ ▷ _) ≫ uncurry ((quotientSKernelZeroFunctorParameter h ≫
    zeroFunctorFullSDiagramFamily A C) ≫ simplicialSSetDiagramProjection _ _ n)) ≫ _
  simp only [Category.assoc]
  erw [zeroFunctorFullSDiagramFamily_projection]
  erw [← uncurry_natural_right, Category.assoc, zeroFunctorFullSCoreFamily_ι,
    ← Category.assoc]

end SerrePositivity.KST.Fibration
