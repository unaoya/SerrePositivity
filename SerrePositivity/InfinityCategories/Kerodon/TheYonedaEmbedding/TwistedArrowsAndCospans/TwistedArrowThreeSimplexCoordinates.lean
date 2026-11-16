module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Tactic.FinCases
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseWeightReindexCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection
/-!
概要：twisted-arrow の一辺を表す三単体の四つの辺を、同じ重みの座標で照合する。
方針：既存の左右の包含・面の座標と、三単体の三辺の合成則を使う。
規約：任意の単体集合で述べ、Kan 性や模型構造を仮定しない。
使われ方：同じ corrected pairing の元の単位と射影を計算するための前提の法則。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 標準単体の指定した二頂点を結ぶ既存の辺を、端点つきで読む。 -/
def twistedSquareStdEdge (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    SSet.Edge (X := (Δ[n] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm i) (stdSimplex.obj₀Equiv.symm j) :=
  SSet.Edge.ofTruncated
    { edge := stdSimplex.edge n i j h
      src_eq := by apply stdSimplex.obj₀Equiv.injective; rfl
      tgt_eq := by apply stdSimplex.obj₀Equiv.injective; rfl }

/-- 標準単体の三頂点の三角形は指定した二辺の合成を表す。 -/
def twistedSquareStdTriangle (n : ℕ) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    SSet.Edge.CompStruct (twistedSquareStdEdge n i j hij)
      (twistedSquareStdEdge n j k hjk) (twistedSquareStdEdge n i k (hij.trans hjk)) := by
  refine SSet.Edge.CompStruct.mk (stdSimplex.triangle i j k hij hjk) ?_ ?_ ?_
  all_goals
    apply ULift.ext
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext a
    fin_cases a <;> rfl

/-- 標準三単体の連続する三辺の合成は外側の辺になる。 -/
lemma twistedSquareStd_three_composite :
    HomotopyCategory.homMk (twistedSquareStdEdge.{u} 3 0 1 (by decide)) ≫
      HomotopyCategory.homMk (twistedSquareStdEdge 3 1 2 (by decide)) ≫
        HomotopyCategory.homMk (twistedSquareStdEdge 3 2 3 (by decide)) =
      HomotopyCategory.homMk (twistedSquareStdEdge 3 0 3 (by decide)) := by
  rw [← Category.assoc,
    HomotopyCategory.homMk_comp_homMk (twistedSquareStdTriangle 3 0 1 2 (by decide) (by decide))]
  exact HomotopyCategory.homMk_comp_homMk
    (twistedSquareStdTriangle 3 0 2 3 (by decide) (by decide))

/-- 同じ三単体を写した後も、三辺の合成則を保つ。 -/
lemma twistedSquare_three_composite {C : SSet.{u}} (σ : (Δ[3] : SSet.{u}) ⟶ C) :
    HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 1 (by decide)).map σ) ≫
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 1 2 (by decide)).map σ) ≫
        HomotopyCategory.homMk ((twistedSquareStdEdge 3 2 3 (by decide)).map σ) =
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 3 (by decide)).map σ) := by
  have h := congrArg (fun f => (SSet.mapHomotopyCategory σ).map f) twistedSquareStd_three_composite
  simp only [Functor.map_comp, SSet.mapHomotopyCategory_map_homMk] at h
  change HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 1 (by decide)).map σ) ≫
    HomotopyCategory.homMk ((twistedSquareStdEdge 3 1 2 (by decide)).map σ) ≫
      HomotopyCategory.homMk ((twistedSquareStdEdge 3 2 3 (by decide)).map σ) =
    HomotopyCategory.homMk ((twistedSquareStdEdge 3 0 3 (by decide)).map σ) at h
  exact h
/-- twisted-arrow の始点の面は三単体の内側の辺に対応する。 -/
lemma twistedSquare_source_order :
    edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (1 : Fin 2)) =
      (stdSimplex.edge 3 1 2 (by decide)).down.toOrderHom := by
  apply OrderHom.ext
  funext a
  fin_cases a
  · change edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (1 : Fin 2)) (edgewiseLeftVertex 0 0) = edgewiseLeftVertex 1 0
    rw [edgewiseWeightReindexOrderHom_left]
    rfl
  · change edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (1 : Fin 2)) (edgewiseRightVertex 0 0) = edgewiseRightVertex 1 0
    rw [edgewiseWeightReindexOrderHom_right]
    rfl

/-- twisted-arrow の終点の面は三単体の外側の辺に対応する。 -/
lemma twistedSquare_target_order :
    edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (0 : Fin 2)) =
      (stdSimplex.edge 3 0 3 (by decide)).down.toOrderHom := by
  apply OrderHom.ext
  funext a
  fin_cases a
  · change edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (0 : Fin 2)) (edgewiseLeftVertex 0 0) = edgewiseLeftVertex 1 1
    rw [edgewiseWeightReindexOrderHom_left]
    rfl
  · change edgewiseWeightReindexOrderHom.{u} (SimplexCategory.δ (n := 0) (0 : Fin 2)) (edgewiseRightVertex 0 0) = edgewiseRightVertex 1 1
    rw [edgewiseWeightReindexOrderHom_right]
    rfl

/-- 同じ重みの表示の逆を使い、twisted-arrow の辺を三単体として読む。 -/
def twistedSquareThreeSimplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (Δ[3] : SSet.{u}) ⟶ C := (edgewiseWeightIso 1).inv ≫ s

/-- 同じ重みの始点の面を三単体の内側の辺と厳密に照合する。 -/
lemma twistedSquare_source_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (edgewiseWeightIso 0).inv ≫ (TwistedArrow C).δ 1 s =
      stdSimplex.map (stdSimplex.edge 3 1 2 (by decide)).down ≫ twistedSquareThreeSimplex s := by
  have h := edgewiseWeightReindexOrderHom_map.{u} (SimplexCategory.δ (n := 0) (1 : Fin 2))
  rw [twistedSquare_source_order] at h
  change stdSimplex.map (stdSimplex.edge 3 1 2 (by decide)).down =
    edgewiseWeightStandardMap (SimplexCategory.δ (n := 0) (1 : Fin 2)) at h
  have hw := congrArg (fun f => f ≫ (edgewiseWeightIso 1).inv) h
  dsimp only [edgewiseWeightStandardMap] at hw
  simp only [show (edgewiseWeightIso (0 + 1)).hom = (edgewiseWeightIso 1).hom from rfl, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hw
  change (edgewiseWeightIso 0).inv ≫ (edgewiseWeight.map
    (SimplexCategory.δ (n := 0) (1 : Fin 2)) ≫ s) = _
  simpa only [twistedSquareThreeSimplex, Category.assoc] using
    congrArg (fun f => f ≫ s) hw.symm

/-- 同じ重みの終点の面を三単体の外側の辺と厳密に照合する。 -/
lemma twistedSquare_target_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    (edgewiseWeightIso 0).inv ≫ (TwistedArrow C).δ 0 s =
      stdSimplex.map (stdSimplex.edge 3 0 3 (by decide)).down ≫ twistedSquareThreeSimplex s := by
  have h := edgewiseWeightReindexOrderHom_map.{u} (SimplexCategory.δ (n := 0) (0 : Fin 2))
  rw [twistedSquare_target_order] at h
  change stdSimplex.map (stdSimplex.edge 3 0 3 (by decide)).down =
    edgewiseWeightStandardMap (SimplexCategory.δ (n := 0) (0 : Fin 2)) at h
  have hw := congrArg (fun f => f ≫ (edgewiseWeightIso 1).inv) h
  dsimp only [edgewiseWeightStandardMap] at hw
  simp only [show (edgewiseWeightIso (0 + 1)).hom = (edgewiseWeightIso 1).hom from rfl, Category.assoc, Iso.hom_inv_id, Category.comp_id] at hw
  change (edgewiseWeightIso 0).inv ≫ (edgewiseWeight.map
    (SimplexCategory.δ (n := 0) (0 : Fin 2)) ≫ s) = _
  simpa only [twistedSquareThreeSimplex, Category.assoc] using
    congrArg (fun f => f ≫ s) hw.symm

open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 同じ重みの左包含を三単体の最初の辺と照合する。 -/
lemma twistedSquare_left_inclusion :
    (stdSimplex.opIso ⦋1⦌).inv ≫ joinInl (Δ[1] : SSet.{u}).op Δ[1] =
      stdSimplex.map (stdSimplex.edge 3 0 1 (by decide)).down ≫ (edgewiseWeightIso 1).inv := by
  apply (cancel_mono (edgewiseWeightIso 1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [edgewiseWeightIso_inl, Iso.inv_hom_id_assoc]
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  fin_cases a <;> rfl

/-- 同じ重みの右包含を三単体の最後の辺と照合する。 -/
lemma twistedSquare_right_inclusion :
    joinInr (Δ[1] : SSet.{u}).op Δ[1] =
      stdSimplex.map (stdSimplex.edge 3 2 3 (by decide)).down ≫ (edgewiseWeightIso 1).inv := by
  apply (cancel_mono (edgewiseWeightIso 1).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [edgewiseWeightIso_inr]
  congr 1
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  fin_cases a <;> rfl

/-- 元の左射影を反転表示から戻すと同じ三単体の最初の辺になる。 -/
lemma twistedSquare_left_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    SSet.yonedaEquiv.symm (SSet.opObjEquiv ((edgewiseLeft C).app _ s)) =
      stdSimplex.map (stdSimplex.edge 3 0 1 (by decide)).down ≫ twistedSquareThreeSimplex s := by
  change SSet.yonedaEquiv.symm (SSet.opObjEquiv (SSet.opObjEquiv.symm
    (SSet.yonedaEquiv ((stdSimplex.opIso ⦋1⦌).inv ≫ joinInl _ _ ≫ s)))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  rw [← Category.assoc, twistedSquare_left_inclusion, Category.assoc]
  rfl

/-- 元の右射影は同じ三単体の最後の辺になる。 -/
lemma twistedSquare_right_simplex {C : SSet.{u}} (s : (TwistedArrow C) _⦋1⦌) :
    SSet.yonedaEquiv.symm ((edgewiseRight C).app _ s) =
      stdSimplex.map (stdSimplex.edge 3 2 3 (by decide)).down ≫ twistedSquareThreeSimplex s := by
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (joinInr _ _ ≫ s)) = _
  rw [Equiv.symm_apply_apply, twistedSquare_right_inclusion, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
