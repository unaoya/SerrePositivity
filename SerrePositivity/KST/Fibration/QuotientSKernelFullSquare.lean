module
public import SerrePositivity.KST.Fibration.QuotientSKernelFullSKanAction
public import SerrePositivity.KST.Fibration.QuotientSKernelZeroFunctorMap
public import SerrePositivity.KST.Fibration.QuotientSKernelTriangles

/-!
概要：元の商核四角形の相対零角を、同じ全 S• の実現へ厳密に読み替える。
方針：元の核の単体的同型を使い、包含と商核上辺の既存の全単体等号を適用する。
規約：元の四射と全二胞体を持つ実四角形を作る。指定 Verdier 側との比較は別工程。
使われ方：K-6 c4 の全四角形比較の商核側。核円柱の元の全 S• 表示を保つ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)

/-- 同じ元の core 包含・商と全 S• 零値作用を四辺に持つ、実現後の厳密四角形。 -/
theorem quotientSKernelFullRealizationSquare :
    CommSq (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
      (simplicialDiagonalFunctor.map (coreSExactMap i))
      (simplicialDiagonalFunctor.map (zeroFunctorFullSMap
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
        (verdierSequenceComposite_zero h)))
      (simplicialDiagonalFunctor.map (coreSExactMap q)) := by
  constructor
  rw [← relativeSKernelSimplicialIso_realization_core h, Category.assoc,
    ← Functor.map_comp, ← quotientSKernelTop_zeroFunctorFullSMap h]
  exact (quotientSKernelRealizationSquare i q).w

/-- 同じ全 S• 零角と元の四射による、一つの全 Ex∞ coherent 四角形。 -/
def quotientSKernelFullInfinitySquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  exInfinityCommSqInfinitySquare (quotientSKernelFullRealizationSquare h)

/-- 同じ相対 S 核の Kan 値から同じ全 S• Kan 値への実同型。 -/
def quotientSKernelCornerFullSKanIso :
    exInfinityClosedKanEnrichedFunctor.obj ⟨simplicialDiagonalFunctor.obj
      (relativeSimplicialSConstruction (i.hom ≫ q.hom))⟩ ≅ fullSRealizationKanObject A where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (relativeSKernelSimplicialIso h).hom)
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (relativeSKernelSimplicialIso h).inv)
  hom_inv_id := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = 𝟙 _
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id]
    simp only [CategoryTheory.Functor.map_id]
  inv_hom_id := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = 𝟙 _
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (𝟙 (simplicialSConstruction A.obj))) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj)))
    rw [CategoryTheory.Functor.map_id simplicialDiagonalFunctor]
    exact CategoryTheory.Functor.map_id _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _

/-- 同じ零角同型と元の商核左辺の合成は、同じ元の full S• core 包含に厳密一致。 -/
theorem quotientSKernelCornerFullSKanIso_left :
    exInfinityKanMap (simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom))) ≫
        (quotientSKernelCornerFullSKanIso h).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _
  rw [← Functor.map_comp, relativeSKernelSimplicialIso_realization_core]

/-- 同じ零角同型と元の全 S• 零値作用の合成は、元の商核上辺に厳密一致。 -/
theorem quotientSKernelCornerFullSKanIso_top :
    (quotientSKernelCornerFullSKanIso h).hom ≫
      exInfinityKanMap (simplicialDiagonalFunctor.map (zeroFunctorFullSMap
        (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
        (verdierSequenceComposite_zero h))) =
      exInfinityKanMap (simplicialDiagonalFunctor.map
        (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _
  rw [← Functor.map_comp, ← Functor.map_comp, ← quotientSKernelTop_zeroFunctorFullSMap]
  rfl

end SerrePositivity.KST.Fibration
