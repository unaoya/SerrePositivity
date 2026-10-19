module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberNullHomotopy
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeSquare

/-! # shifted cone の dg nerve 内の実四角形

概要：cone(f)[−1]→M→N と零角を実二単体で貼る。
方針：射影の合成の原始元を下三角形の成分として使う。
規約：この段階では引き戻し性を主張しない。使われ方：β3 の fiber 境界充填。
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

/-- 射影と元の射の合成の零ホモトピーを持つ下三角形。 -/
def dgModuleFiberLowerTriangle (f : M ⟶ N) :
    SSet.Edge.CompStruct (dgModuleEdge A D (dgModuleFiberProjection A D f))
      (dgModuleEdge A D f)
      (dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶ N)) :=
  dgModuleCompStruct A D (dgModuleFiberProjection A D f) f 0
    (dgModuleFiberNullHomotopy A D f) (by
      change _ = _ - 0
      rw [sub_zero]
      exact dgModuleFiberNullHomotopy_differential A D f)

/-- 零加群を経由する上三角形。 -/
def dgModuleFiberUpperTriangle (f : M ⟶ N) :
    SSet.Edge.CompStruct
      (dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶
        moduleZero A D)) (dgModuleEdge A D (0 : moduleZero A D ⟶ N))
      (dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶ N)) :=
  dgModuleCompStruct A D 0 0 0 0 (by rw [zero_comp, sub_self]; exact map_zero _)

/-- shifted cone の射影と零ホモトピーが定める実四角形。 -/
def dgModuleFiberSquare (f : M ⟶ N) : Δ[1] ⊗ Δ[1] ⟶ dgModuleNerve A D :=
  square_isPushout.desc (SSet.yonedaEquiv.symm (dgModuleFiberUpperTriangle A D f).simplex)
    (SSet.yonedaEquiv.symm (dgModuleFiberLowerTriangle A D f).simplex) (by
      rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        (dgModuleFiberUpperTriangle A D f).d₁, (dgModuleFiberLowerTriangle A D f).d₁])

/-- shifted cone 四角形の下三角形。 -/
lemma dgModuleFiberSquare_lower (f : M ⟶ N) :
    squareTriangle 1 ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleFiberLowerTriangle A D f).simplex :=
  square_isPushout.inr_desc _ _ _

/-- shifted cone 四角形の上三角形。 -/
lemma dgModuleFiberSquare_upper (f : M ⟶ N) :
    squareTriangle 0 ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleFiberUpperTriangle A D f).simplex :=
  square_isPushout.inl_desc _ _ _

/-- 下辺は shifted cone の射影の実際の辺。 -/
lemma dgModuleFiberSquare_bottom (f : M ⟶ N) :
    squareBottomEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (dgModuleFiberProjection A D f)).edge := by
  rw [← cofiberSquareTriangle_bottomEdge, Category.assoc, dgModuleFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberLowerTriangle A D f).d₂]

/-- 左辺は元の対象から零加群への辺。 -/
lemma dgModuleFiberSquare_left (f : M ⟶ N) :
    squareLeftEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D
      (0 : ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶
        moduleZero A D)).edge := by
  rw [← cofiberSquareTriangle_leftEdge, Category.assoc, dgModuleFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberUpperTriangle A D f).d₂]

/-- 右辺は元の dg 加群射の実際の辺。 -/
lemma dgModuleFiberSquare_right (f : M ⟶ N) :
    squareRightEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D f).edge := by
  rw [← squareTriangle_rightEdge, Category.assoc, dgModuleFiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberLowerTriangle A D f).d₀]

/-- 上辺は零加群から元の標的への辺。 -/
lemma dgModuleFiberSquare_top (f : M ⟶ N) :
    squareTopEdge ≫ dgModuleFiberSquare A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (0 : moduleZero A D ⟶ N)).edge := by
  rw [← squareTriangle_topEdge, Category.assoc, dgModuleFiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (dgModuleFiberUpperTriangle A D f).d₀]

/-- 四角形の始点は shifted cone。 -/
lemma dgModuleFiberSquare_vertex00 (f : M ⟶ N) :
    squareVertex (dgModuleFiberSquare A D f) 0 0 = Simplex.vertex (dgModuleFiber A D f) := by
  rw [← squareBottomEdge_source, dgModuleFiberSquare_bottom, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D (dgModuleFiberProjection A D f)).src_eq

/-- 下辺の終点は元の始点加群。 -/
lemma dgModuleFiberSquare_vertex10 (f : M ⟶ N) :
    squareVertex (dgModuleFiberSquare A D f) 1 0 =
      Simplex.vertex (ForgetEnrichment.to (Complex A) M) := by
  rw [← squareBottomEdge_target, dgModuleFiberSquare_bottom, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D (dgModuleFiberProjection A D f)).tgt_eq

/-- 四角形の終点は元の標的加群。 -/
lemma dgModuleFiberSquare_vertex11 (f : M ⟶ N) :
    squareVertex (dgModuleFiberSquare A D f) 1 1 =
      Simplex.vertex (ForgetEnrichment.to (Complex A) N) := by
  rw [← squareRightEdge_target, dgModuleFiberSquare_right, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D f).tgt_eq

/-- 四角形の (0,1) の角は具体的な零加群。 -/
lemma dgModuleFiberSquare_vertex01 (f : M ⟶ N) :
    squareVertex (dgModuleFiberSquare A D f) 0 1 = dgModuleNerveZeroVertex A D := by
  rw [← squareLeftEdge_target, dgModuleFiberSquare_left, Equiv.apply_symm_apply]
  exact (dgModuleEdge A D (0 : ForgetEnrichment.of (Complex A) (dgModuleFiber A D f) ⟶
    moduleZero A D)).tgt_eq

/-- shifted cone の実際の零角付き四角形。 -/
def dgModuleFiberZeroTriangle (f : M ⟶ N) : ZeroTriangle (dgModuleNerve A D) where
  square := dgModuleFiberSquare A D f
  zero_corner := by
    rw [dgModuleFiberSquare_vertex01]
    exact dgModuleNerveZeroVertex_isZero A D

/-- 標準 fiber 四角形を cospan の実際の錐として読む。 -/
def dgModuleFiberCone (f : M ⟶ N) :
    JoinCone (pullbackCospan (dgModuleFiberSquare A D f)) :=
  pullbackCone (dgModuleFiberSquare A D f)

end SerrePositivity.InfinityCategories
