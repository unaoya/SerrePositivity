module
public import SerrePositivity.KST.NonConnective.DGKappaConeCofinality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CellDGResolutionNerve

/-!
概要：同じ cone の完備化前の K 零性を、D-9 の同じ実平坦源へ戻す。
方針：元の cell 増大と対象ラベルの上げ下げを native 同値として保持する。
規約：同じ I・Z と共終性命題に条件付き。元の平坦源・増大を変更しない。
使われ方：K-6 c5・K-7 c5 の完備化前の連結 fibration の中央項。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実 cone の対象ラベルの上げ下げを、元の nerve の実同型として保持する。
方針：D 正本の元の二つの dg 関手と厳密合成式を nerve に写す。
規約：同じ cone に限る。一般の宇宙移送 API は新設しない。
使われ方：同じ cell 増大の像を元の Yoneda 始域へ照合する。 -/
def dgKappaConeNativeLiftIso : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGKappaCone R D I) ≅
    (dgKappaConeYonedaSource R D I).carrier where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (DGKappaCone R D I))
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (DGKappaCone R D I))
  hom_inv_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
  inv_hom_id := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown_comp_up, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
    rfl

/-- 概要：D-9 の同じ実平坦源を、完備化前の native 安定模型として保持する。
方針：元の cone の cell 分解の前三角性から安定性を得る。
規約：Perf 完備化をこの中央模型へ混ぜない。
使われ方：元の実核・実商との完備化前の連結 fibration。 -/
def dgKappaNativeResolvedCone : StableModel.{max (u + 1) v} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGCategoryCellResolution.Source R (DGKappaCone R D I))
  stable := by
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R
      (DGCategoryCellResolution.Source R (DGKappaCone R D I))

/-- 概要：同じ実平坦源と元の cone の Yoneda 始域は、元の増大を順方向に含む同値。
方針：D 正本の cell 増大の全写像空間同値と元のラベル移送だけを合成する。
規約：新たな dg 屋根や射影を選ばない。
使われ方：構成済みの同じ cone の K 零性を実平坦源へ反映する。 -/
def dgKappaNativeResolvedConeEquivalence :
    StableModelEquivalence (dgKappaNativeResolvedCone R D I) (dgKappaConeYonedaSource R D I) := by
  let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionNerveEquivalence R (DGKappaCone R D I)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (dgKappaConeNativeLiftIso R D I))
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨⟨e.hom, preservesCofiberData_of_isExactFunctor _⟩,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor _⟩, e.homInvIso, e.invHomIso⟩

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

include hcofinal in
/-- 概要：同じ実平坦源の完備化前の K の全整数群は、共終性供給に条件付きで自明。
方針：元の増大を含む同じ完全同値の K 射の単射性で、元の cone の K 零性を反映する。
規約：同じ I・Z を使い、完備化前の商の K 零性は主張しない。
使われ方：完備化前の連結 fibration の実中央項の零性。 -/
theorem dgKappaNativeResolvedConeK_subsingleton (Z : DGKappaZeroInput R D I) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (dgKappaNativeResolvedCone R D I)) j) := by
  let := dgKappaConeNativeK_subsingleton R D I hcofinal Z j
  exact (kSpectrumMap_piIsomorphism_of_equivalence
    (dgKappaNativeResolvedConeEquivalence R D I) j).1.subsingleton

end SerrePositivity.KST.NonConnective
