module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：同じ図式上の slice の辺と、二つの錐の脚の合成三角形。
方針：slice の元の一次単体を一頂点で制限し、標準二単体へ正規化する。
規約：比較辺も各脚も元の一単体を保持する。使われ方：BF fiber の比較と包含の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ConeEdgeLeg

variable {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p}
  (a : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) c d) (k : K _⦋0⦌)

/-- 元の slice の一単体と指定された図式頂点の張る三角形。 -/
def triangle : (Δ[2] : SSet.{u}) ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[1]) (SSet.yonedaEquiv.symm k) ≫ a.edge.val

/-- 二つの面は元の両端の錐の脚。 -/
lemma face (i : Fin 2) :
    stdSimplex.δ i.castSucc ≫ triangle a k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ i a.edge).val := by
  have hi : stdSimplex.δ i.castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 (Δ[0] : SSet.{u})) := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).1
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex i]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [triangle, ← Category.assoc, hi]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0])) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[1]) (SSet.yonedaEquiv.symm k) ≫ a.edge.val =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm k)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 K) ≫ a.edge.val
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 (Δ[0] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[1]) (SSet.yonedaEquiv.symm k) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 K) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  simpa only [Category.assoc] using
    congrArg (fun q ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ q ≫ a.edge.val) hj

/-- 残る面は slice 射影による元の比較辺。 -/
lemma comparison_face :
    stdSimplex.δ (2 : Fin 3) ≫ triangle a k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] K ≫ a.edge.val := by
  rw [triangle, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]

/-- 比較辺と比較先の脚の合成は、元の錐の脚になる。 -/
def compStruct : SSet.Truncated.Edge.CompStruct
    (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) where
  simplex := SSet.yonedaEquiv (triangle a k)
  d₂ := by
    change X.δ 2 (SSet.yonedaEquiv (triangle a k)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, comparison_face]
    rfl
  d₀ := by
    change X.δ 0 (SSet.yonedaEquiv (triangle a k)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have hf : stdSimplex.δ (0 : Fin 3) ≫ triangle a k = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ d.val :=
      (face a k 0).trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ z.val)
        a.tgt_eq)
    exact (congrArg SSet.yonedaEquiv hf).trans (SSet.yonedaEquiv_comp _ _)
  d₁ := by
    change X.δ 1 (SSet.yonedaEquiv (triangle a k)) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    have hf : stdSimplex.δ (1 : Fin 3) ≫ triangle a k = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ c.val :=
      (face a k 1).trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneLegInclusion k ≫ z.val)
        a.src_eq)
    exact (congrArg SSet.yonedaEquiv hf).trans (SSet.yonedaEquiv_comp _ _)

lemma homMk_naturality :
    SSet.Truncated.HomotopyCategory.homMk
        (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg d k) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c k) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (compStruct a k)

/-- 三頂点の表示を同時に替えても、元の三辺の類の合成式は保たれる。 -/
lemma homMk_comp_transport {A : SSet.{u}} {x y z x' y' z' : A _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj A) x y)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj A) y z)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj A) x z)
    (e' : SSet.Truncated.Edge (X := (truncation 2).obj A) x' y')
    (f' : SSet.Truncated.Edge (X := (truncation 2).obj A) y' z')
    (g' : SSet.Truncated.Edge (X := (truncation 2).obj A) x' z')
    (h : SSet.Truncated.HomotopyCategory.homMk e ≫ SSet.Truncated.HomotopyCategory.homMk f =
      SSet.Truncated.HomotopyCategory.homMk g)
    (hx : x = x') (hy : y = y') (hz : z = z')
    (he : e.edge = e'.edge) (hf : f.edge = f'.edge) (hg : g.edge = g'.edge) :
    SSet.Truncated.HomotopyCategory.homMk e' ≫ SSet.Truncated.HomotopyCategory.homMk f' =
      SSet.Truncated.HomotopyCategory.homMk g' := by
  subst x' y' z'
  have he' : e = e' := SSet.Truncated.Edge.ext he
  have hf' : f = f' := SSet.Truncated.Edge.ext hf
  have hg' : g = g' := SSet.Truncated.Edge.ext hg
  simpa only [← he', ← hf', ← hg'] using h

end SerrePositivity.KST.LocalizingInvariants.ConeEdgeLeg
