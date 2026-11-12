module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.EpsilonWordRigidity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellUnitNonzero
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.QuotientEpsilonCriterion

/-!
概要：cell 分解を標的とする固定 ε 整合パラメータの、null 対象での成分を検査する。
方針：単位係数の次数別分裂を、独立 ε の単語・次数分離に適用する。
規約：全 native map の不存在は主張しない。既存の ε 整合条件の必要帰結。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded HomologicalComplex KST.SConstruction
open DGCategoryCellResolution
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (S : Set C) (T : Set (Source R D))
  (F G : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NullPreservingFunctorsε R C (Source R D) S T)

/-- 固定 ε 整合の成分は、非零次数または異なる null 像対象では零に限られる。 -/
lemma quotientEpsilonCellParameter_component_zero
    {K : Complex R} (u : K ⟶ dgFunctorHom R C (Source R D) F.val G.val)
    (hε : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonCompatible R C (Source R D) S T F G u)
    (b : S) (q : ℤ) (t : K.X q)
    (hc : q ≠ 0 ∨ F.val.obj b.val ≠ G.val.obj b.val) :
    ((u ≫ dgFunctorHomπ R C (Source R D) F.val G.val b.val).f q) t = 0 := by
  have h := hε b q t
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonOriginalParameter_app] at h
  let x : T := ⟨F.val.obj b.val, F.property b.val b.property⟩
  let y : T := ⟨G.val.obj b.val, G.property b.val b.property⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.epsilon_original_component_zero R (Source R D) T x y q
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellUnitScalar R D x.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellUnitScalar_unit R D x.val)
    (((u ≫ dgFunctorHomπ R C (Source R D) F.val G.val b.val).f q) t) hc h

/-- ε Hom 内の全ての非零次数は、各元 null 対象への評価で零になる。 -/
lemma quotientEpsilonCellHom_component_zero_of_degree_ne_zero
    (b : S) (q : ℤ) (hq : q ≠ 0)
    (t : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C (Source R D) S T F G).X q) :
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι R C (Source R D) S T F G ≫
      dgFunctorHomπ R C (Source R D) F.val G.val b.val).f q) t = 0 := by
  have hε := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHomι_compatible R C (Source R D) S T F G
    (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C (Source R D) S T F G))
  rw [Category.id_comp] at hε
  exact quotientEpsilonCellParameter_component_zero R C D S T F G _ hε b q t (Or.inl hq)

/-- null 対象が一つあれば、ε 関手圏の単位は境界にならない（同じ ε Hom 複体内）。 -/
lemma quotientEpsilonCell_unit_not_boundary [Nontrivial R] (b : S) :
    ¬ ∃ t : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C (Source R D) S T F F).X (-1),
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C (Source R D) S T F F).d (-1) 0 t =
        (unitElement R F).val := by
  rintro ⟨t, ht⟩
  let E := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.nullPreservingFunctorsεForget R C (Source R D) S T).comp
    (dgFunctorEvaluationDG R C (Source R D) b.val)
  let e := E.map F F
  have hz : e.f (-1) t = 0 :=
    quotientEpsilonCellHom_component_zero_of_degree_ne_zero R C D S T F F b (-1) (by omega) t
  have he := E.map_unitElement R F
  have hd := (ConcreteCategory.congr_hom (e.comm (-1) 0) t).symm
  change e.f 0 ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.quotientEpsilonHom R C (Source R D) S T F F).d (-1) 0 t) =
    (homObject R (Source R D) (F.val.obj b.val) (F.val.obj b.val)).d (-1) 0 (e.f (-1) t) at hd
  rw [ht, hz, map_zero] at hd
  have hu : (unitElement R (F.val.obj b.val)).val = 0 := he.symm.trans hd
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellResolution_unit_ne_zero R D (F.val.obj b.val) hu

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
