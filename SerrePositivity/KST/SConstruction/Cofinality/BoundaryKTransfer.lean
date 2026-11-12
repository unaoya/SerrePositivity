module
public import SerrePositivity.KST.SConstruction.Cofinality.BoundaryKanTransfer

/-!
概要：元の境界 Kan 射の次数条件を元の境界 K 射の次数条件へ移す。
方針：零次数を含む既存の loop の自然な次数移動で元の射を照合する。
規約：元の raw K 零段と実 kSpectrumMap を保持する。
使われ方：相対 fiber 比較の最後の群条件の輸送。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 概要：境界 Kan 射の π₁ 単射・高次全単射は元の境界 K 射の零次単射・正次数全単射。
方針：元の loop の全次数の自然な同値を両側から消去する。
規約：元の raw K 零段の誘導写像の条件。
使われ方：元の実 kSpectrumMap の主結論への接続。 -/
lemma boundaryK_groupConditions_of_boundaryKan {X Y : StableModel.{u}} (f : X ⟶ Y)
    (h : Function.Injective (pointedHomotopyMap 1 ((boundaryKanRealizationFunctor 0).map f)) ∧
      ∀ n : ℕ, 1 < n →
        Function.Bijective (pointedHomotopyMap n ((boundaryKanRealizationFunctor 0).map f))) :
    (∀ n : ℕ, 0 < n → Function.Bijective ((rawKStageHomotopyFunctor 0 n).map f)) ∧
      Function.Injective ((rawKStageHomotopyFunctor 0 0).map f) := by
  let A := (boundaryKanRealizationFunctor 0).obj X
  let B := (boundaryKanRealizationFunctor 0).obj Y
  let p : A ⟶ B := (boundaryKanRealizationFunctor 0).map f
  let : KanComplex ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).obj A).right :=
    loopSpace_kanComplex A
  let : KanComplex ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).obj B).right :=
    loopSpace_kanComplex B
  let l := (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map p
  let eX (n : ℕ) := loopHomotopyEquiv A n
  let eY (n : ℕ) := loopHomotopyEquiv B n
  have hm (n : ℕ) : (eY n) ∘ (pointedHomotopyMap n l) =
      (pointedHomotopyMap (n + 1) p) ∘ (eX n) := by
    funext a
    exact loopHomotopyEquiv_natural p n a
  change (∀ n : ℕ, 0 < n → Function.Bijective (pointedHomotopyMap n l)) ∧
    Function.Injective (pointedHomotopyMap 0 l)
  constructor
  · intro n hn
    apply (Function.Bijective.of_comp_iff' (eY n).bijective _).mp
    exact (congrArg Function.Bijective (hm n)).mpr
      ((h.2 (n + 1) (by omega)).comp (eX n).bijective)
  · apply (Function.Injective.of_comp_iff (eY 0).injective _).mp
    exact (congrArg Function.Injective (hm 0)).mpr (h.1.comp (eX 0).injective)

/-- 概要：元の core S 実現の群条件から同じ元の実 K 射の共終性条件を得る。
方針：境界商・Kan 比較・loop の自然な次数移動と実 BF 段比較を合成する。
規約：元の指定完全射の kSpectrumMap を結論する。
使われ方：相対 fiber の供給を消費した後の主結論の公開。 -/
theorem kSpectrumMap_cofinality_of_coreS {X Y : StableModel.{u}} (f : X ⟶ Y)
    (h : ∀ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (coreSRealizationFunctor.obj X)) _⦋0⦌,
      Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map f))
        (x := a) rfl) ∧
      ∀ n : ℕ, 1 < n → Function.Bijective
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSRealizationFunctor.map f)) (x := a) rfl)) :
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) :=
  (kSpectrumMap_cofinality_iff_boundary f).mpr
    (boundaryK_groupConditions_of_boundaryKan f (boundaryKan_groupConditions_of_coreS f h))

end SerrePositivity.KST.SConstruction.Cofinality
