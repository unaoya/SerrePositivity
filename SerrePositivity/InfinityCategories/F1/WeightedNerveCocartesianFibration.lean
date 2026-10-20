module

public import SerrePositivity.InfinityCategories.F1.WeightedNerveCocartesianCriterion
public import SerrePositivity.InfinityCategories.F1.CartesianFibration

/-!
概要：quasicategory 値 weighted nerve の射影は cocartesian fibration。
方針：一次ホーンの係数を定値な辺で充填し、その係数を保つ持ち上げを使う。
規約：始点と底の辺を厳密に固定し、係数の Kan 性は要求しない。
使われ方：Cat∞ 値の通常圏上の unstraightening と scaffold による復元。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

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

/-- 元の quasicategory 値 weighted nerve の射影は cocartesian fibration。 -/
instance weightedNerveProjection_cocartesianFibration {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    CocartesianFibration (weightedNerveProjection F) where
  mem := by
    refine ⟨InnerFibration.mem, ?_⟩
    intro x e he
    have sq : CommSq (SSet.const x) (horn 1 0).ι (weightedNerveProjection F) e := by
      constructor
      apply horn.hom_ext'
      intro j hj
      fin_cases j
      · exact (hj rfl).elim
      · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc]
        change SSet.const ((weightedNerveProjection F).app _ x) = stdSimplex.δ 1 ≫ e
        rw [he, SSet.yonedaEquiv_symm_zero]
    let σ := SSet.yonedaEquiv e
    have hσ : SSet.yonedaEquiv.symm σ = e := SSet.yonedaEquiv.symm_apply_apply _
    have ha : SSet.const x ≫ weightedNerveProjection F =
        (horn 1 0).ι ≫ SSet.yonedaEquiv.symm σ := by rw [hσ]; exact sq.w
    obtain ⟨v, hv⟩ := exists_initial_oneHorn_constant_filler
      (weightedNerveHornLastCoefficient F σ 0 (SSet.const x) ha)
    obtain ⟨ψ, hp, ht, hlast⟩ :=
      exists_weightedNerveHorn_candidate_with_last_of_coefficient_filler
        F σ 0 (by decide) (SSet.const x) ha (SSet.const v) hv
    let s : weightedNerveSimplex F 1 := ⟨σ, ψ⟩
    let H : (Δ[1] : SSet.{u}) ⟶ weightedNerve F := SSet.yonedaEquiv.symm s
    refine ⟨H, ?_, ?_, ?_⟩
    · have hf := weightedNerveHorn_candidate_face_agreement F σ 0 (by decide)
        (SSet.const x) ha ψ hp ht 1 (by decide)
      calc
        stdSimplex.δ 1 ≫ H = SSet.yonedaEquiv.symm
            (weightedNerveSimplexMap F (SimplexCategory.δ 1) s) :=
          SSet.yonedaEquiv_symm_naturality_left (X := weightedNerve F) (SimplexCategory.δ 1) s
        _ = horn.ι 0 1 (by decide) ≫ SSet.const x := by
          rw [hf, SSet.yonedaEquiv.symm_apply_apply]
        _ = SSet.yonedaEquiv.symm x := by
          rw [SSet.comp_const, SSet.yonedaEquiv_symm_zero]
    · rw [SSet.yonedaEquiv_symm_comp]
      exact hσ
    · rw [SSet.yonedaEquiv.apply_symm_apply]
      apply isCocartesianEdge_weightedNerve_of_coefficient
      change IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (ψ.app (Fin.last 1))))
      rw [hlast]
      exact isInvertibleEdge_map_const _ 0

end SerrePositivity.InfinityCategories
