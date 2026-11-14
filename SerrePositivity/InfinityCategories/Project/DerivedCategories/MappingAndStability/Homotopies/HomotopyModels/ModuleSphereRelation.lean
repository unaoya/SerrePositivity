module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ModuleSphereBoundary

/-! # 線形写像空間の充填関係と Moore 境界

概要：境界零単体のホモトピー関係は差が Moore 境界となることと同値である。
方針：充填単体から零番目の退化を引き、逆に Moore 単体へ退化を足す。
規約：隣接する零番目と一番目の面を使う。使われ方：π と Moore ホモロジーの商の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] (W : SimplicialObject (ModuleCat.{v} S))

/-- 概要：零番目の隣接面の充填の面を線形座標で評価する。
方針：充填の三種類の面の条件へ Yoneda 評価を適用する。
規約：面 0 は f、面 1 は g、他は零。使われ方：差から Moore 境界を作る。 -/
lemma moduleRelStruct_faces {n : ℕ}
    {f g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).PtSimplex (n + 1) 0}
    (h : SSet.PtSimplex.RelStruct f g 0) :
    W.δ 0 (SSet.yonedaEquiv h.map) = SSet.yonedaEquiv f.map ∧
    W.δ 1 (SSet.yonedaEquiv h.map) = SSet.yonedaEquiv g.map ∧
    ∀ j : Fin (n + 3), 1 < j → W.δ j (SSet.yonedaEquiv h.map) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := congrArg SSet.yonedaEquiv h.δ_castSucc_map
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp] at hh
    change W.δ ((0 : Fin (n + 2)).castSucc) (SSet.yonedaEquiv h.map) =
      SSet.yonedaEquiv f.map at hh
    simpa only [Fin.castSucc_zero] using hh
  · have hh := congrArg SSet.yonedaEquiv h.δ_succ_map
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp] at hh
    change W.δ ((0 : Fin (n + 2)).succ) (SSet.yonedaEquiv h.map) =
      SSet.yonedaEquiv g.map at hh
    simpa only [Fin.succ_zero_eq_one] using hh
  · intro j hj
    have hh := congrArg SSet.yonedaEquiv (h.δ_map_of_gt j hj)
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.module_yoneda_const_zero] at hh
    exact hh

/-- 概要：充填関係は二つの球面単体の差が Moore 境界となることと同値。
方針：t−s₀g と u+s₀g を相互に構成する。
規約：正次数 n+1、全ての面の条件を保つ。使われ方：ホモトピー群の商と線形商の同定。 -/
theorem moduleRelStruct_iff_boundary {n : ℕ}
    (f g : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).PtSimplex (n + 1) 0) :
    Nonempty (SSet.PtSimplex.RelStruct f g 0) ↔
      ∃ u : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W (n + 2),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphereBoundaryMap W n u = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n f -
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n g := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n f
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pointedModuleSimplexEquiv W n g
  constructor
  · rintro ⟨h⟩
    obtain ⟨h₀, h₁, hrest⟩ := moduleRelStruct_faces W h
    have h₀' : W.δ 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSimplexValue W (n + 2) (SSet.yonedaEquiv h.map)) = F.val := h₀
    have h₁' : W.δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSimplexValue W (n + 2) (SSet.yonedaEquiv h.map)) = G.val := h₁
    have hrest' (j : Fin (n + 3)) (hj : 1 < j) :
        W.δ j (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSimplexValue W (n + 2) (SSet.yonedaEquiv h.map)) = 0 := hrest j hj
    let u : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W (n + 2) :=
      ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSimplexValue W (n + 2) (SSet.yonedaEquiv h.map)) - W.σ 0 G.val,
        (Submodule.mem_iInf _).2 (fun j => by
        change W.δ j.succ (_ - _) = 0
        rw [map_sub, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
        by_cases hj : j = 0
        · subst j
          change W.δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSimplexValue W (n + 2) (SSet.yonedaEquiv h.map)) - G.val = 0
          rw [h₁', sub_self]
        · have hs : 1 < j.succ := by
            simp only [Fin.lt_def, Fin.val_succ, Fin.ext_iff, Fin.val_zero, Fin.val_one] at hj ⊢
            omega
          rw [hrest' _ hs]
          have hn₀ : j.succ ≠ (0 : Fin (n + 2)).castSucc := by simp
          have hn : j.succ ≠ (0 : Fin (n + 2)).succ := by
            exact fun e => hj (Fin.succ_injective _ e)
          simp only [hn₀, hn, ite_false, sub_self])⟩
    refine ⟨u, Subtype.ext ?_⟩
    change W.δ 0 (_ - _) = F.val - G.val
    rw [map_sub]
    rw [h₀', _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
    simp only [Fin.castSucc_zero, ite_true]
  · rintro ⟨u, hu⟩
    have hu₀ : W.δ 0 u.val = F.val - G.val := congrArg Subtype.val hu
    let t := u.val + W.σ 0 G.val
    have ht₀ : W.δ 0 t = F.val := by
      dsimp only [t]
      rw [map_add, hu₀, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
      simp
    have ht₁ : W.δ 1 t = G.val := by
      dsimp only [t]
      rw [map_add, show W.δ (1 : Fin (n + 3)) u.val = 0 from
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreKernelModule_face W u (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
      simp
    have htrest (j : Fin (n + 3)) (hj : 1 < j) : W.δ j t = 0 := by
      have hne : j ≠ 0 := by intro e; subst j; simp at hj
      have he : (j.pred hne).succ = j := Fin.succ_pred j hne
      dsimp only [t]
      rw [map_add, ← he, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreKernelModule_face, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sphericalModule_degeneracy_face]
      have hn₀ : (j.pred hne).succ ≠ (0 : Fin (n + 2)).castSucc := by
        rw [he]; intro e; subst j; simp at hj
      have hn₁ : (j.pred hne).succ ≠ (0 : Fin (n + 2)).succ := by
        rw [he]; intro e; subst j; simp at hj
      simp only [hn₀, hn₁, ite_false, add_zero]
    refine ⟨{ map := SSet.yonedaEquiv.symm t
              δ_castSucc_map := ?_
              δ_succ_map := ?_
              δ_map_of_lt := ?_
              δ_map_of_gt := ?_ }⟩
    · apply SSet.yonedaEquiv.injective
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact ht₀
    · apply SSet.yonedaEquiv.injective
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact ht₁
    · intro j hj
      exact False.elim (not_lt_of_ge (Fin.zero_le j) hj)
    · intro j hj
      apply SSet.yonedaEquiv.injective
      rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.module_yoneda_const_zero]
      exact htrest j hj

end SerrePositivity.InfinityCategories.Project.DerivedCategories
