module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSquareRefinement
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.CommutativeSquareRealization

/-!
概要：有限 cospan 上の同じ実錐から、正方形の底辺・左辺を元の実脚として回収する。
方針：点と辺の join の面公式を、既存の錐・正方形同型の二三角形へ代入する。
規約：全て実単体写像の厳密等式であり、同じ脚を選び直さない。
使われ方：右分数を添付した有限錐から、共有辺を持つ二つの実四角形を取り出す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 辺の始点への錐脚は、同じ辺を底とする錐三角形の最初の辺。 -/
lemma coneLegInclusion_edge_source {K : SSet.{u}} (f : (Δ[1] : SSet.{u}) ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ f)) =
      stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) f := by
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u}))
      (stdSimplex.δ (1 : Fin 2)) = stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).inv := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2) ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (stdSimplex.δ (1 : Fin 2)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) f := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion, Equiv.symm_apply_apply, hj, ← Category.assoc, hv]
  exact Category.assoc _ _ _

/-- 錐の正方形の同じ底辺は cospan の零番目の頂点への元の脚。 -/
lemma cospanConeSquare_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.{u}.inv =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂)) := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [coneLegInclusion_edge_source]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge = stdSimplex.δ (2 : Fin 3) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 錐の正方形の同じ左辺は cospan の一番目の頂点への元の脚。 -/
lemma cospanConeSquare_left : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.{u}.inv =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂)) := by
  apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [coneLegInclusion_edge_source]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge = stdSimplex.δ (2 : Fin 3) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right]
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 錐脚の形状写像への自然性は、同じ標準辺の厳密等式。 -/
lemma coneLegInclusion_naturality {K L : SSet.{u}} (f : K ⟶ L) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (f.app (Opposite.op ⦋0⦌) k) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion, Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, SSet.yonedaEquiv_symm_comp]

/-- 同じ全錐の形状制限は、指定頂点への実脚の一次単体を厳密に保つ。 -/
lemma nativeConeLeg_restriction {K L X : SSet.{u}} {p : K ⟶ X} {q : L ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (f : L ⟶ K)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) f ≫ c.val = d.val) (k : L _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c (f.app (Opposite.op ⦋0⦌) k)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k).edge := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (f.app (Opposite.op ⦋0⦌) k) ≫ c.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ d.val := by
    rw [← coneLegInclusion_naturality, Category.assoc, h]
  change c.val.app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (f.app (Opposite.op ⦋0⦌) k))) =
      d.val.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k))
  simpa only [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv he

/-- 同じ終点を持つ二本の実辺図式を、元の cospan として厳密に貼る。 -/
def conePairCospan {K : SSet.{u}} (a b : (Δ[1] : SSet.{u}) ⟶ K)
    (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) : (horn 2 2 : SSet.{u}) ⟶ K :=
  horn₂₂.isPushout.desc a b h

lemma conePairCospan_first {K : SSet.{u}} (a b : (Δ[1] : SSet.{u}) ⟶ K)
    (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    horn₂₂.ι₀₂ ≫ conePairCospan a b h = a := horn₂₂.isPushout.inl_desc _ _ _

lemma conePairCospan_second {K : SSet.{u}} (a b : (Δ[1] : SSet.{u}) ⟶ K)
    (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    horn₂₂.ι₁₂ ≫ conePairCospan a b h = b := horn₂₂.isPushout.inr_desc _ _ _

/-- 同じ全錐の二つの隣接辺への制限から、そのまま読み出す実四角形。 -/
def conePairSquare {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (a b : (Δ[1] : SSet.{u}) ⟶ K) (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (conePairCospan a b h) ≫ c.val

lemma conePairSquare_cospan {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (a b : (Δ[1] : SSet.{u}) ⟶ K) (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ conePairSquare c a b h = conePairCospan a b h ≫ p := by
  simp only [conePairSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, c.property]

lemma conePairSquare_right {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (a b : (Δ[1] : SSet.{u}) ⟶ K) (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ conePairSquare c a b h = a ≫ p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, Category.assoc, conePairSquare_cospan,
    ← Category.assoc, conePairCospan_first]

lemma conePairSquare_top {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (a b : (Δ[1] : SSet.{u}) ⟶ K) (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ conePairSquare c a b h = b ≫ p := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, Category.assoc, conePairSquare_cospan,
    ← Category.assoc, conePairCospan_second]

lemma conePairSquare_bottom {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (a b : (Δ[1] : SSet.{u}) ⟶ K) (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ conePairSquare c a b h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a)) ≫ c.val := by
  have hv : (conePairCospan a b h).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂)) =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ a) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, conePairCospan_first]
  simp only [conePairSquare, ← Category.assoc]
  rw [cospanConeSquare_bottom, coneLegInclusion_naturality, hv]

lemma conePairSquare_left {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (a b : (Δ[1] : SSet.{u}) ⟶ K) (h : stdSimplex.δ 0 ≫ a = stdSimplex.δ 0 ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ conePairSquare c a b h =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ b)) ≫ c.val := by
  have hv : (conePairCospan a b h).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂)) =
      SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ b) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, conePairCospan_second]
  simp only [conePairSquare, ← Category.assoc]
  rw [cospanConeSquare_left, coneLegInclusion_naturality, hv]

variable {X : SSet.{u}} {p : (horn 2 2 : SSet.{u}) ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)

lemma coneSquare_bottom_leg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫ c.val := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge, Category.assoc]
  change stdSimplex.δ (2 : Fin 3) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv) ≫ c.val) = _
  rw [ht, ← Category.assoc]
  change (stdSimplex.δ ((1 : Fin 2).succ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneTriangleInclusion horn₂₂.ι₀₂) ≫ c.val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneTriangleInclusion_face, Category.assoc]

lemma coneSquare_left_leg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare c =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫ c.val := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_leftEdge, Category.assoc]
  change stdSimplex.δ (2 : Fin 3) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv) ≫ c.val) = _
  rw [ht, ← Category.assoc]
  change (stdSimplex.δ ((1 : Fin 2).succ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneTriangleInclusion horn₂₂.ι₁₂) ≫ c.val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneTriangleInclusion_face, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants
