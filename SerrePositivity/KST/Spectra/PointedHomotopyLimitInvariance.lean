module

public import SerrePositivity.KST.Spectra.PointedHomotopyLimit
public import SerrePositivity.KST.Spectra.KanEquivalenceBridge

/-!
概要：点つき Bousfield–Kan end は成分ごとの全基点 π_* 同型を保つ。
方針：本レーンの Whitehead から実際のホモトピー同値へ移し、end の path 分解の比較を適用する。
規約：π_n の意味は L9 所有の定義。∞ 極限の普遍性は用いない。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。hG と Tot の Ω 条件。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open SerrePositivity.InfinityCategories


namespace SerrePositivity.KST.Spectra.PointedHomotopyLimit

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：成分ごとの全基点 π_* 同型は点つき end でも全基点 π_* 同型。
方針：成分の点つき Whitehead、既存の自然な path 置換、全単射 RLP による比較をつなぐ。
規約：添字圏や遷移の fibration 性に追加仮定を課さない。
使われ方：BF 1978 §2、HA §1.4.2。構造随伴射の end への移送。 -/
theorem map_piIsomorphism {I : Type u} [SmallCategory I]
    {D E : I ⥤ PointedSimplicialSet.{u}}
    [∀ i, KanComplex (D.obj i).right] [∀ i, KanComplex (E.obj i).right]
    (τ : D ⟶ E) (hτ : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (τ.app i).right) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (map τ).right := by
  let : ∀ i, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (D.obj i).right)
  let : ∀ i, KanComplex ((E ⋙ PointedSimplicialSet.forget).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (E.obj i).right)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_homotopyEquivalence
    (Functor.whiskerRight τ PointedSimplicialSet.forget)
    (fun i ↦ pointed_piIsomorphism_homotopyEquivalence (τ.app i) (hτ i))
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (Functor.whiskerRight τ PointedSimplicialSet.forget))
  exact kanPiIsomorphism_of_qCatEquivalence _ h.isQCatEquivalence

end

end SerrePositivity.KST.Spectra.PointedHomotopyLimit
