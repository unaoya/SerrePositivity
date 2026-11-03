module
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleComponents
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberSquare
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.InfinityCategories.Stable.SuspensionSquare

/-! # dg 加群の実際の cone 四角形

概要：M→N、M→0、N→cone(f)、0→cone(f) を二単体で整合的に貼る。
方針：次数 −1 の左包含を下三角形のホモトピーに使い、上三角形は零で埋める。
規約：この段階では押し出し性を主張しない。使われ方：β3 の cofiber の境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- cone の左包含を合成の零ホモトピーとして持つ下三角形。 -/
def dgModuleConeLowerTriangle (f : M ⟶ N) :
    SSet.Edge.CompStruct (dgModuleEdge A D f) (dgModuleEdge A D (moduleConeInr A D f))
      (dgModuleEdge A D (0 : M ⟶ moduleCone A D f)) :=
  dgModuleCompStruct A D f (moduleConeInr A D f) 0 (moduleConeInlElement A D f) (by
    have hz : (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      (0 : M ⟶ moduleCone A D f))).val = 0 := rfl
    rw [hz, sub_zero]
    exact moduleConeInlElement_d A D f)

/-- 零対象を経由する上三角形。 -/
def dgModuleConeUpperTriangle (f : M ⟶ N) :
    SSet.Edge.CompStruct (dgModuleEdge A D (0 : M ⟶ moduleZero A D))
      (dgModuleEdge A D (0 : moduleZero A D ⟶ moduleCone A D f))
      (dgModuleEdge A D (0 : M ⟶ moduleCone A D f)) :=
  dgModuleCompStruct A D 0 0 0 0 (by rw [zero_comp, sub_self]; exact map_zero _)

/-- dg 加群の標準 cone を零角と二つの実二単体で表す四角形。 -/
def dgModuleConeSquare (f : M ⟶ N) : Δ[1] ⊗ Δ[1] ⟶ dgModuleNerve A D :=
  square_isPushout.desc (SSet.yonedaEquiv.symm (dgModuleConeUpperTriangle A D f).simplex)
    (SSet.yonedaEquiv.symm (dgModuleConeLowerTriangle A D f).simplex) (by
      rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        (dgModuleConeUpperTriangle A D f).d₁, (dgModuleConeLowerTriangle A D f).d₁])

/-- 標準 cone 四角形の下三角形。 -/
lemma dgModuleConeSquare_lower (f : M ⟶ N) :
    squareTriangle 1 ≫ dgModuleConeSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleConeLowerTriangle A D f).simplex :=
  square_isPushout.inr_desc _ _ _

/-- 標準 cone 四角形の上三角形。 -/
lemma dgModuleConeSquare_upper (f : M ⟶ N) :
    squareTriangle 0 ≫ dgModuleConeSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleConeUpperTriangle A D f).simplex :=
  square_isPushout.inl_desc _ _ _

/-- 下辺は元の dg 加群射の実際の辺。 -/
lemma dgModuleConeSquare_bottom (f : M ⟶ N) :
    squareBottomEdge ≫ dgModuleConeSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D f).edge := by
  rw [← cofiberSquareTriangle_bottomEdge, Category.assoc, dgModuleConeSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleConeLowerTriangle A D f).d₂]

/-- 左辺は元の対象から零加群への辺。 -/
lemma dgModuleConeSquare_left (f : M ⟶ N) :
    squareLeftEdge ≫ dgModuleConeSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (0 : M ⟶ moduleZero A D)).edge := by
  rw [← cofiberSquareTriangle_leftEdge, Category.assoc, dgModuleConeSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleConeUpperTriangle A D f).d₂]

/-- 右辺は標準の cone 包含の実際の辺。 -/
lemma dgModuleConeSquare_right (f : M ⟶ N) :
    squareRightEdge ≫ dgModuleConeSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (moduleConeInr A D f)).edge := by
  rw [← squareTriangle_rightEdge, Category.assoc, dgModuleConeSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleConeLowerTriangle A D f).d₀]

/-- 上辺は零加群から cone への辺。 -/
lemma dgModuleConeSquare_top (f : M ⟶ N) :
    squareTopEdge ≫ dgModuleConeSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (0 : moduleZero A D ⟶ moduleCone A D f)).edge := by
  rw [← squareTriangle_topEdge, Category.assoc, dgModuleConeSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleConeUpperTriangle A D f).d₀]

/-- 標準四角形の始点は元の加群。 -/
lemma dgModuleConeSquare_vertex00 (f : M ⟶ N) :
    squareVertex (dgModuleConeSquare A D f) 0 0 =
      Simplex.vertex (ForgetEnrichment.to (Complex A) M) := by
  rw [← squareBottomEdge_source, dgModuleConeSquare_bottom, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D f).src_eq

/-- 標準四角形の下辺の終点は元の標的加群。 -/
lemma dgModuleConeSquare_vertex10 (f : M ⟶ N) :
    squareVertex (dgModuleConeSquare A D f) 1 0 =
      Simplex.vertex (ForgetEnrichment.to (Complex A) N) := by
  rw [← squareBottomEdge_target, dgModuleConeSquare_bottom, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D f).tgt_eq

/-- 標準四角形の終点は実際の cone 加群。 -/
lemma dgModuleConeSquare_vertex11 (f : M ⟶ N) :
    squareVertex (dgModuleConeSquare A D f) 1 1 =
      Simplex.vertex (ForgetEnrichment.to (Complex A) (moduleCone A D f)) := by
  rw [← squareRightEdge_target, dgModuleConeSquare_right, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D (moduleConeInr A D f)).tgt_eq

/-- 四角形の (0,1) の角は具体的な零加群。 -/
lemma dgModuleConeSquare_vertex01 (f : M ⟶ N) :
    squareVertex (dgModuleConeSquare A D f) 0 1 = dgModuleNerveZeroVertex A D := by
  rw [← squareLeftEdge_target, dgModuleConeSquare_left, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D (0 : M ⟶ moduleZero A D)).tgt_eq

/-- 標準 cone 四角形は実際の零角付き四角形を与える。 -/
def dgModuleConeZeroTriangle (f : M ⟶ N) : ZeroTriangle (dgModuleNerve A D) where
  square := dgModuleConeSquare A D f
  zero_corner := by
    rw [dgModuleConeSquare_vertex01]
    exact dgModuleNerveZeroVertex_isZero A D

/-- 標準 cone 四角形を span の実際の余錐として読む。 -/
def dgModuleConeCocone (f : M ⟶ N) :
    JoinCocone (pushoutSpan (dgModuleConeSquare A D f)) := pushoutCocone (dgModuleConeSquare A D f)

end SerrePositivity.InfinityCategories
