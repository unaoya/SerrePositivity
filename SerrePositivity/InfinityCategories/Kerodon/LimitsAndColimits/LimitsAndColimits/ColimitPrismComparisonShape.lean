module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitPrismTotalShape

/-!
概要：元の始点余錐から全図式の余錐の制限への比較を、同じ prism の形状から構成する。
方針：join と直積の座標を保ち、元の両端と頂点の射を厳密に照合する。
規約：底 K は任意の単体集合。使われ方：HTT 5.5.4.5(2) の余極限閉性。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 左の点を時刻零に固定し、右の区間の時刻を保つ射。 -/
def colimitPrismInitialTime : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[1] ⟶ Δ[1] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ stdSimplex.σ (0 : Fin 2)

/-- 比較の時刻の左端は零である。 -/
lemma colimitPrismInitialTime_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ colimitPrismInitialTime =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  fin_cases i
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j
  rfl

/-- 比較の時刻の右端は元の区間を保つ。 -/
lemma colimitPrismInitialTime_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ colimitPrismInitialTime = 𝟙 Δ[1] := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
  fin_cases i <;> rfl

/-- 始点余錐と全図式の余錐の制限を結ぶ形状の射。 -/
def colimitPrismComparisonMap (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 Δ[1]) ≫
      colimitPrismInitialTime)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))))

/-- 比較の左因子は元の始点図式の包含を保つ。 -/
lemma colimitPrismComparisonMap_inl (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[1] ≫ colimitPrismComparisonMap K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [colimitPrismComparisonMap, Category.assoc, lift_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, colimitPrismInitialTime_inl, SSet.comp_const,
      Category.assoc, whiskerLeft_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst]
  · rw [colimitPrismComparisonMap, Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
      Category.assoc, whiskerLeft_snd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd,
      Category.id_comp]

/-- 比較の右因子は元の prism の頂点の区間そのもの。 -/
lemma colimitPrismComparisonMap_inr (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[1] ≫ colimitPrismComparisonMap K =
      lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u})))) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [colimitPrismComparisonMap, Category.assoc, lift_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp, colimitPrismInitialTime_inr, lift_fst]
  · rw [colimitPrismComparisonMap, Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      SSet.const_comp, lift_snd]
    have hv : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply SSet.stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    rw [hv, ← SSet.yonedaEquiv_comp, Category.id_comp]

/-- 比較区間の始点は元の始点余錐への包含。 -/
lemma colimitPrismComparisonMap_source (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.δ (1 : Fin 2)) ≫ colimitPrismComparisonMap K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) := by
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_hom_ext_stdSimplex
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
      exact congrArg (fun t ↦ t ≫ fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]))
        ((colimitPrismComparisonMap_inl K).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))))
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap]
      have he := congrArg (fun t ↦ stdSimplex.δ (1 : Fin 2) ≫ t ≫
        fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])) (colimitPrismComparisonMap_inr K)
      simp only [Category.assoc, lift_fst, Category.comp_id] at he
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_fst, SSet.comp_const,
        stdSimplex.δ_one_eq_const] using he
  · rw [colimitPrismComparisonMap, Category.assoc, lift_snd, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
    have h : stdSimplex.δ (1 : Fin 2) ≫
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = 𝟙 (Δ[0] : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    simp only [Category.comp_id, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd]

/-- 比較区間の終点は全図式の余錐の始点面への制限。 -/
lemma colimitPrismComparisonMap_target (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.δ (0 : Fin 2)) ≫ colimitPrismComparisonMap K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K) (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismTotalMap K := by
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCone_hom_ext_stdSimplex
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
      have hs := congrArg (fun t ↦ t ≫ fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]))
        (colimitPrismComparisonMap_inl K)
      have ht := congrArg (fun t ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ t) ≫
        fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismTotalMap_inl K)
      exact hs.trans (by simpa only [Category.assoc] using ht.symm)
    · simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
      have hs := congrArg (fun t ↦ stdSimplex.δ (0 : Fin 2) ≫ t ≫
        fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])) (colimitPrismComparisonMap_inr K)
      have ht := congrArg (fun t ↦ t ≫ fst (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismTotalMap_inr K)
      simp only [Category.assoc, lift_fst, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const,
        stdSimplex.δ_zero_eq_const] at hs ht
      simpa only [Category.assoc, stdSimplex.δ_zero_eq_const] using hs.trans ht.symm
  · rw [colimitPrismComparisonMap, Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitPrismTotalMap,
      Category.assoc, lift_snd, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
    have h : stdSimplex.δ (0 : Fin 2) ≫
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = 𝟙 (Δ[0] : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    simp only [Category.comp_id, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
