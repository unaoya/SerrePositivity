module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.NullHomotopyRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.PathCollapseBase

/-!
概要：指定部分 path 上で path 方向に定値な、filtered な底の共通収縮を選ぶ。
方針：部分 path をパラメータへ潰した有限押し出し上で収縮し、両脚へ制限する。
規約：模型と部分パラメータの元の底射を保持し、全円柱の因子分解を厳密に返す。
使われ方：元の境界引き戻し射を全 path とともに輸送する相対有限検出。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：共通底の収縮を、指定部分 path 上ではそのパラメータの収縮から選べる。
方針：底の有限押し出し上の一つの収縮を、模型と部分パラメータへ制限する。
規約：部分 path の底の全円柱は厳密に定値方向へ因子分解。使われ方：元の境界の同時輸送。 -/
lemma exists_nullHomotopy_with_collapsed_path {A M B : SSet.{u}}
    [A.Finite] [M.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (k : (Δ[1] : SSet.{u}) ⊗ A ⟶ M) (r : M ⟶ B) (a : A ⟶ B)
    (h : k ≫ r = snd (Δ[1] : SSet.{u}) A ≫ a) :
    ∃ b : B _⦋0⦌, ∃ H : SSet.Homotopy r (SSet.const b),
      ∃ J : SSet.Homotopy a (SSet.const b),
        (k ▷ (Δ[1] : SSet.{u})) ≫ H.h =
          (snd (Δ[1] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫ J.h := by
  obtain ⟨b, ⟨L⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_nullHomotopy_of_isFilteredInfinity (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseMap k r a h)
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nullHomotopyRestriction L (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseModel k) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseMap_model k r a h)
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nullHomotopyRestriction L (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseParameter k)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseMap_parameter k r a h)
  refine ⟨b, H, J, ?_⟩
  change (k ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseModel k ▷ (Δ[1] : SSet.{u})) ≫ L.h =
    (snd (Δ[1] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBaseParameter k ▷ (Δ[1] : SSet.{u})) ≫ L.h
  rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pathCollapseBase_condition, comp_whiskerRight, Category.assoc]

/-- 概要：path 定値な底円柱の端点制限は、部分パラメータの元の円柱に一致する。
方針：全 path の円柱式を指定端点で制限する。
規約：全時刻で厳密に一致。使われ方：二入力の相対輸送の底条件。 -/
lemma collapsedPathCylinder_endpoint {A K M B : SSet.{u}}
    (k : (Δ[1] : SSet.{u}) ⊗ A ⟶ M) (i : A ⟶ K) (j : K ⟶ M) (e : Fin 2)
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint e A ≫ k = i ≫ j)
    (R : M ⊗ (Δ[1] : SSet.{u}) ⟶ B) (S : A ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hR : (k ▷ (Δ[1] : SSet.{u})) ≫ R =
      (snd (Δ[1] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫ S) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ (j ▷ (Δ[1] : SSet.{u})) ≫ R = S := by
  have h := congrArg (fun r ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint e A ▷ (Δ[1] : SSet.{u})) ≫ r) hR
  rw [← comp_whiskerRight_assoc, hj, comp_whiskerRight_assoc] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
