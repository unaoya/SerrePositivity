module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorResolvedInput
public import SerrePositivity.KST.SConstruction.DGKInputPerfectNu
public import SerrePositivity.KST.LocalizingInvariants.PathComparisonSquare
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
概要：固定 ν の cell 屋根の回収二胞体を、そのまま Cat^perf の全四角形に実現する。
方針：指定した増大の単位二胞体から比較三角形を作り、同じ全単体を持ち上げる。
規約：S 内の増大の厳密な逆を要求しない。完備化後の射に strict 商性を課さない。
使われ方：resolved 射影の固定 ν 境界と、元 gluing の値との実比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "a" => dgOdotMilnorAugmentationExactMap R d
local notation "r" => dgOdotMilnorResolvedProjectionNu R d
local notation "q" => dgOdotMilnorCellProjectionExactMap R d

/-- 概要：固定 ν の屋根回収を保持する同じ指定比較三角形。
方針：増大同値の単位二胞体を写像空間で実現する。規約：射の類だけに落とさない。
使われ方：元 cell 商包含を固定する対角の移送。 -/
def dgOdotMilnorRoofComparisonTriangle : SSet.Edge.CompStruct
    (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R (dgOdotMilnorCellInput R d))))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKInputStableValue R (dgOdotMilnorCellInput R d))
      (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) from
        ⟨(a).hom ≫ (r).hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (a).hom (r).hom⟩)) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.exactMapComparisonTriangle (F := q)
    (G := ⟨(a).hom ≫ (r).hom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp (a).hom (r).hom⟩)
    (dgOdotMilnorResolvedProjectionNu_roof R d).symm

/-- 概要：固定 ν の屋根と同じ cell 商包含を持つ実全四角形。
方針：指定比較三角形を同じ恒等左辺の三角形へ貼る。規約：四辺を保持する。
使われ方：元 gluing の値へ戻した resolved 商射影の実境界。 -/
def dgOdotMilnorRoofRawSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} :=
  PathComparisonSquare.square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (a) (r))
    (SSet.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q))) (dgOdotMilnorRoofComparisonTriangle R d)

/-- 概要：同じ実全四角形の四辺は元増大・cell 商包含・恒等・屋根。
方針：指定三角形を保持した構成の四辺を回収する。規約：全一単体の等号。
使われ方：固定 ν の二辺の指定比較。 -/
lemma dgOdotMilnorRoofRawSquare_edges :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgOdotMilnorRoofRawSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (a)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorRoofRawSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorRoofRawSquare R d = SSet.yonedaEquiv.symm
        (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (dgKInputStableValue R (dgOdotMilnorCellInput R d)))).edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgOdotMilnorRoofRawSquare R d =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (r)).edge :=
  ⟨PathComparisonSquare.square_bottom _ _ _, PathComparisonSquare.square_top _ _ _,
    PathComparisonSquare.square_left _ _ _, PathComparisonSquare.square_right _ _ _⟩

/-- 概要：元の屋根四角形の四角は同じ固定 ν 入力値であり完備。
方針：四辺の端点を回収し D の Perf 完備性を適用する。
規約：native 商の完備性とは区別する。使われ方：全単体を保つ持ち上げ。 -/
lemma dgOdotMilnorRoofRawSquare_corner_complete (i j : Fin 2) :
    perfectStableVertexPredicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgOdotMilnorRoofRawSquare R d) i j) := by
  have he := dgOdotMilnorRoofRawSquare_edges R d
  have h00 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (dgOdotMilnorRoofRawSquare R d)
  rw [he.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (a)).src_eq] at h00
  have h10 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (dgOdotMilnorRoofRawSquare R d)
  rw [he.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (a)).tgt_eq] at h10
  have h01 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source (dgOdotMilnorRoofRawSquare R d)
  rw [he.2.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (q)).src_eq] at h01
  have h11 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (dgOdotMilnorRoofRawSquare R d)
  rw [he.2.2.2, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (r)).tgt_eq] at h11
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject _).obj
  fin_cases i <;> fin_cases j
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
      (dgOdotMilnorRoofRawSquare R d) 0 0)).obj
    rw [← h00, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact dgKInputStableValue_isIdempotentComplete R _
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
      (dgOdotMilnorRoofRawSquare R d) 0 1)).obj
    rw [← h01, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact dgKInputStableValue_isIdempotentComplete R _
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
      (dgOdotMilnorRoofRawSquare R d) 1 0)).obj
    rw [← h10, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact dgKInputStableValue_isIdempotentComplete R _
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
      (dgOdotMilnorRoofRawSquare R d) 1 1)).obj
    rw [← h11, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact dgKInputStableValue_isIdempotentComplete R _

/-- 概要：同じ全四角形の全頂点が Cat^perf の頂点条件を満たす。
方針：元の四角の判定へ帰着する。規約：任意の零単体を扱う。
使われ方：全部分複体への持ち上げの入力。 -/
lemma dgOdotMilnorRoofRawSquare_vertex_complete
    (x : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) _⦋0⦌) :
    perfectStableVertexPredicate ((dgOdotMilnorRoofRawSquare R d).app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨x, y⟩ := x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  exact dgOdotMilnorRoofRawSquare_corner_complete R d i j

/-- 概要：同じ指定二胞体と全四辺を持つ Cat^perf の実屋根比較面。
方針：同じ全単体を全部分複体へ持ち上げる。規約：面を選び直さない。
使われ方：完備化付き相対提示との固定 ν 境界の照合。 -/
def dgOdotMilnorRoofPerfectSquare :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ perfectStableInfinity.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift perfectStableVertexPredicate (dgOdotMilnorRoofRawSquare R d)
    (dgOdotMilnorRoofRawSquare_vertex_complete R d)

/-- 概要：Cat^perf 包含後は同じ全屋根比較面を厳密に回収する。
方針：全部分複体の包含則。規約：全単体の等号。
使われ方：元の四辺・比較三角形の保存。 -/
lemma dgOdotMilnorRoofPerfectSquare_inclusion :
    dgOdotMilnorRoofPerfectSquare R d ≫ perfectStableInfinityInclusion =
      dgOdotMilnorRoofRawSquare R d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.KST.SConstruction
