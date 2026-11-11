module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance

/-!
概要：L9 所有の全基点 π_* 同型と既存の単体的ホモトピー同値の比較。
方針：点つき Whitehead と、可逆 path 置換の全単射 RLP による span を使う。
規約：モデル構造や HT-KQ を使わない。π_n の定義と全単射の結論は本レーンが所有する。
使われ方：BF 1978 §2、Goerss–Jardine I §7、Kerodon 4.8.4.1（Tag 01JX）。段ごとの end の同型不変性。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：点つき Kan 複体間の全基点 π_* 同型は実際の単体的ホモトピー同値。
方針：点つき Whitehead の逆を選び、写像空間の成分を対称にして区間ホモトピーを戻す。
規約：逆射は元の点つき射の実際のホモトピー逆。
使われ方：Goerss–Jardine I §7、Kerodon 4.8.4.1（Tag 01JX）。end の係数の比較への入力。 -/
theorem pointed_piIsomorphism_homotopyEquivalence
    {X Y : PointedSimplicialSet.{u}} [KanComplex X.right] [KanComplex Y.right]
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f.right := by
  obtain ⟨g, ⟨HX, hX⟩, ⟨HY, hY⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopyInverse f hf
  have hCX : PointedMapping.componentOf (𝟙 X) = PointedMapping.componentOf (f ≫ g) :=
    (PointedMapping.piZero_eq_iff_pointedHomotopy (𝟙 X) (f ≫ g)).mpr ⟨HX, hX⟩
  have hCY : PointedMapping.componentOf (𝟙 Y) = PointedMapping.componentOf (g ≫ f) :=
    (PointedMapping.piZero_eq_iff_pointedHomotopy (𝟙 Y) (g ≫ f)).mpr ⟨HY, hY⟩
  obtain ⟨HX', _⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy (f ≫ g) (𝟙 X)).mp hCX.symm
  obtain ⟨HY', _⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy (g ≫ f) (𝟙 Y)).mp hCY.symm
  exact ⟨g.right, ⟨HX'⟩, ⟨HY'⟩⟩

/-- 概要：Kan 複体間の既存の圏同値は L9 の全基点 π_* 同型。
方針：可逆 path 置換の二つの全単射 RLP 射とその切断で元の射を分解する。
規約：全基点・零次数を含む本レーンの誘導写像の全単射性。
使われ方：Goerss–Jardine I §7、Kerodon 4.8.4.1（Tag 01JX）。end の比較の結論を L9 の Ω 条件に戻す。 -/
theorem kanPiIsomorphism_of_qCatEquivalence {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection f
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap f
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection f
  have hr : (MorphismProperty.monomorphisms SSet.{u}).rlp r :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := r)
  let : Fibration r := (fibration_iff _).mpr (fun _ _ j hj ↦ hr j (J_le_monomorphisms _ hj))
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement f) := isFibrant_of_fibration r
  have hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q :=
    hf.equivalencePathReplacementMap_trivialKanFibration.mem
  have hri := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight r hr
  have hqi := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight q hq
  have hs : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism s := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := r) _ hri
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_projection]
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id X
  have h := hs.comp hqi
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementSection_map] at h
  exact h

end

end SerrePositivity.KST.Spectra
