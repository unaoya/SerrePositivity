module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.NerveCocartesianCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration

/-!
概要：quasicategory 値 weighted nerve の射影は cocartesian fibration。
方針：一次ホーンの係数を定値な辺で充填し、その係数を保つ持ち上げを使う。
規約：始点と底の辺を厳密に固定し、係数の Kan 性は要求しない。
使われ方：Cat∞ 値の通常圏上の unstraightening と scaffold による復元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 一次ホーンの射は、その唯一の頂点での定値な辺によって充填できる。 -/
lemma exists_initial_oneHorn_constant_filler {X : SSet.{u}}
    (q : (horn 1 0 : SSet.{u}) ⟶ X) :
    ∃ v : X _⦋0⦌, (horn 1 0).ι ≫ SSet.const (X := Δ[1]) v = q := by
  let v := SSet.yonedaEquiv (horn.ι 0 1 (by decide) ≫ q)
  refine ⟨v, ?_⟩
  apply horn.hom_ext'
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · rw [SSet.comp_const]
    exact (SSet.yonedaEquiv_symm_zero v).symm.trans
      (SSet.yonedaEquiv.symm_apply_apply _)

/-- 任意の係数図式で、始点と底の辺を保つ lift を最後の係数が可逆となるように取れる。 -/
lemma exists_weightedNerve_lift_with_invertible_coefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) _⦋0⦌)
    (e : (Δ[1] : SSet.{u}) ⟶ nerve C)
    (he : stdSimplex.δ 1 ≫ e =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app (Opposite.op ⦋0⦌) x)) :
    ∃ H : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      stdSimplex.δ 1 ≫ H = SSet.yonedaEquiv.symm x ∧ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = e ∧
      _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.WeightedNerveCoefficientInvertible F (SSet.yonedaEquiv H) := by
  have sq : CommSq (SSet.const x) (horn 1 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) e := by
    constructor
    apply horn.hom_ext'
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc]
      change SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F).app _ x) = stdSimplex.δ 1 ≫ e
      rw [he, SSet.yonedaEquiv_symm_zero]
  let σ := SSet.yonedaEquiv e
  have hσ : SSet.yonedaEquiv.symm σ = e := SSet.yonedaEquiv.symm_apply_apply _
  have ha : SSet.const x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (horn 1 0).ι ≫ SSet.yonedaEquiv.symm σ := by rw [hσ]; exact sq.w
  obtain ⟨v, hv⟩ := exists_initial_oneHorn_constant_filler
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ 0 (SSet.const x) ha)
  obtain ⟨ψ, hp, ht, hlast⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.exists_weightedNerveHorn_candidate_with_last_of_coefficient_filler
      F σ 0 (by decide) (SSet.const x) ha (SSet.const v) hv
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F 1 := ⟨σ, ψ⟩
  let H : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F := SSet.yonedaEquiv.symm s
  refine ⟨H, ?_, ?_, ?_⟩
  · have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHorn_candidate_face_agreement F σ 0 (by decide)
      (SSet.const x) ha ψ hp ht 1 (by decide)
    calc
      stdSimplex.δ 1 ≫ H = SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ 1) s) :=
        SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (SimplexCategory.δ 1) s
      _ = horn.ι 0 1 (by decide) ≫ SSet.const x := by
        rw [hf, SSet.yonedaEquiv.symm_apply_apply]
      _ = SSet.yonedaEquiv.symm x := by
        rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero]
  · rw [SSet.yonedaEquiv_symm_comp]
    exact hσ
  · rw [SSet.yonedaEquiv.apply_symm_apply]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (ψ.app (Fin.last 1))))
    rw [hlast]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_map_const _ 0

/-- 元の quasicategory 値 weighted nerve の射影は cocartesian fibration。 -/
instance weightedNerveProjection_cocartesianFibration {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x e he
    obtain ⟨H, hsrc, hbase, hi⟩ :=
      exists_weightedNerve_lift_with_invertible_coefficient F x e he
    exact ⟨H, hsrc, hbase, _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.isCocartesianEdge_weightedNerve_of_coefficient F _ hi⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
