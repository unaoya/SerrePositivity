module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberNullHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeSquare

/-! # shifted cone の dg nerve 内の実四角形

概要：cone(f)[−1]→M→N と零角を実二単体で貼る。
方針：射影の合成の原始元を下三角形の成分として使う。
規約：この段階では引き戻し性を主張しない。使われ方：β3 の fiber 境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 射影と元の射の合成の零ホモトピーを持つ下三角形。 -/
def dgModuleFiberLowerTriangle (f : M ⟶ N) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) ⟶ N)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f) f 0
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy A D f) (by
      change _ = _ - 0
      rw [sub_zero]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberNullHomotopy_differential A D f)

/-- 零加群を経由する上三角形。 -/
def dgModuleFiberUpperTriangle (f : M ⟶ N) :
    SSet.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) ⟶
        moduleZero A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (0 : moduleZero A D ⟶ N))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) ⟶ N)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCompStruct A D 0 0 0 0 (by rw [zero_comp, sub_self]; exact map_zero _)

/-- shifted cone の射影と零ホモトピーが定める実四角形。 -/
def dgModuleFiberSquare (f : M ⟶ N) : Δ[1] ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm (dgModuleFiberUpperTriangle A D f).simplex)
    (SSet.yonedaEquiv.symm (dgModuleFiberLowerTriangle A D f).simplex) (by
      rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        (dgModuleFiberUpperTriangle A D f).d₁, (dgModuleFiberLowerTriangle A D f).d₁])

/-- shifted cone 四角形の下三角形。 -/
lemma dgModuleFiberSquare_lower (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleFiberLowerTriangle A D f).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- shifted cone 四角形の上三角形。 -/
lemma dgModuleFiberSquare_upper (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleFiberUpperTriangle A D f).simplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 下辺は shifted cone の射影の実際の辺。 -/
lemma dgModuleFiberSquare_bottom (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSquareTriangle_bottomEdge, Category.assoc, dgModuleFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberLowerTriangle A D f).d₂]

/-- 左辺は元の対象から零加群への辺。 -/
lemma dgModuleFiberSquare_left (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D
      (0 : ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) ⟶
        _root_.SerrePositivity.DifferentialGraded.moduleZero A D)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberSquareTriangle_leftEdge, Category.assoc, dgModuleFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberUpperTriangle A D f).d₂]

/-- 右辺は元の dg 加群射の実際の辺。 -/
lemma dgModuleFiberSquare_right (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, dgModuleFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberLowerTriangle A D f).d₀]

/-- 上辺は零加群から元の標的への辺。 -/
lemma dgModuleFiberSquare_top (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (0 : moduleZero A D ⟶ N)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, dgModuleFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberUpperTriangle A D f).d₀]

/-- 四角形の始点は shifted cone。 -/
lemma dgModuleFiberSquare_vertex00 (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgModuleFiberSquare A D f) 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source, dgModuleFiberSquare_bottom, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).src_eq

/-- 下辺の終点は元の始点加群。 -/
lemma dgModuleFiberSquare_vertex10 (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgModuleFiberSquare A D f) 1 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) M) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target, dgModuleFiberSquare_bottom, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).tgt_eq

/-- 四角形の終点は元の標的加群。 -/
lemma dgModuleFiberSquare_vertex11 (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgModuleFiberSquare A D f) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) N) := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target, dgModuleFiberSquare_right, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).tgt_eq

/-- 四角形の (0,1) の角は具体的な零加群。 -/
lemma dgModuleFiberSquare_vertex01 (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (dgModuleFiberSquare A D f) 0 1 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex A D := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target, dgModuleFiberSquare_left, Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) ⟶
    _root_.SerrePositivity.DifferentialGraded.moduleZero A D)).tgt_eq

/-- shifted cone の実際の零角付き四角形。 -/
def dgModuleFiberZeroTriangle (f : M ⟶ N) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) where
  square := dgModuleFiberSquare A D f
  zero_corner := by
    rw [dgModuleFiberSquare_vertex01]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D

/-- 標準 fiber 四角形を cospan の実際の錐として読む。 -/
def dgModuleFiberCone (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (dgModuleFiberSquare A D f)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgModuleFiberSquare A D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
