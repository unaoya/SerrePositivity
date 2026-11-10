module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.FirstVertexLeftAnodyne
public import SerrePositivity.InfinityCategories.Core.CocartesianCosliceLifting
public import SerrePositivity.InfinityCategories.Core.RelativeInitialEndpoint
public import Mathlib.CategoryTheory.Limits.Preorder
public import SerrePositivity.InfinityCategories.Core.JoinCells
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.PointCosliceEdge
public import SerrePositivity.InfinityCategories.Core.Slice
public import Mathlib.Tactic.CrossRefAttribute

/-! # 可逆辺による相対始対象の輸送
概要：相対始点境界充填を可逆な辺に沿って移すための端点とホーンの比較。
方針：基底の coslice を最初の頂点から持ち上げ、相対 coslice の普遍性で錐を作る。
規約：Core の公開 API は変更しない。使われ方：HTT §1.2.12・§2.1.2、固定零射の cofiber。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects
open _root_.SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial

/-- 概要：辺から作った点の coslice の頂点の射影は元の辺の終点。
方針：辺の表示の逆律に終点の余面を適用する。
規約：周囲の quasicategory 性は不要。使われ方：指定した可逆辺の端点の固定。 -/
lemma pointCosliceVertexOfEdge_projection {X : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ X)
    {y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) (SSet.yonedaEquiv a) y) :
    (sliceUnderProjection a).app (Opposite.op ⦋0⦌) (pointCosliceVertexOfEdge a e) = y := by
  let t := pointCosliceVertexOfEdge a e
  calc
    _ = X.δ 0 (pointCosliceVertexEdge a t).edge := (pointCosliceVertexEdge a t).tgt_eq.symm
    _ = X.δ 0 e.edge := congrArg (X.δ 0) (pointCosliceVertexEdge_ofEdge a e)
    _ = y := e.tgt_eq

/-- 概要：相対始点境界充填条件は、元の quasicategory の可逆辺に沿って保たれる。
方針：基底の coslice を最初の頂点から持ち上げ、相対始対象の coslice で境界上の錐を選ぶ。
その最初の辺の可逆性を相対外側ホーンの充填へ使い、端点へ射影する。
規約：p は quasicategory 間の inner fibration。使われ方：余極限余錐の輸送。 -/
lemma InitialBoundaryLifting.of_invertibleEdge {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (a : (Δ[0] : SSet.{u}) ⟶ X) (ha : InitialBoundaryLifting p (SSet.yonedaEquiv a))
    {y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) (SSet.yonedaEquiv a) y)
    (he : IsInvertibleEdge e) : InitialBoundaryLifting p y := by
  intro n u b hu sq
  let j : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
    SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)))
  let z := pointCosliceVertexOfEdge a e
  let zB := (sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) z
  have hz : (sliceUnderProjection a).app (Opposite.op ⦋0⦌) z = y :=
    pointCosliceVertexOfEdge_projection a e
  have hzB : (sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) zB =
      p.app (Opposite.op ⦋0⦌) y := by
    change p.app (Opposite.op ⦋0⦌) ((sliceUnderProjection a).app (Opposite.op ⦋0⦌) z) = _
    rw [hz]
  have hb₀ : j ≫ b = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) y) := by
    calc
      _ = (boundaryVertex n 0 ≫ (boundary (n + 1)).ι) ≫ b := by rw [boundaryVertex_ι]
      _ = (boundaryVertex n 0 ≫ u) ≫ p := by rw [Category.assoc, ← sq.w, ← Category.assoc]
      _ = _ := by rw [hu, SSet.yonedaEquiv_symm_comp]
  have hsb : CommSq (SSet.yonedaEquiv.symm zB) j (sliceUnderProjection (a ≫ p)) b := by
    constructor
    rw [SSet.yonedaEquiv_symm_comp, hzB]
    exact hb₀.symm
  have : HasLiftingProperty j (sliceUnderProjection (a ≫ p)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.stdSimplex_firstVertex_leftAnodyne (n + 1) _
      (LeftFibration.mem (p := sliceUnderProjection (a ≫ p)))
  let B := hsb.lift
  have hB₀ : j ≫ B = SSet.yonedaEquiv.symm zB := hsb.fac_left
  have hBp : B ≫ sliceUnderProjection (a ≫ p) = b := hsb.fac_right
  have : Mono (boundaryVertex n 0 : (Δ[0] : SSet.{u}) ⟶ boundary (n + 1)) :=
    stdSimplex.isTerminalObj₀.mono_from _
  obtain ⟨C, hC₀, hCu, hCp⟩ := exists_relativeInitialCosliceLift a p ha (boundaryVertex n 0)
    (SSet.yonedaEquiv.symm z) u ((boundary (n + 1)).ι ≫ B) (by
      rw [Category.assoc, hBp]
      exact sq.w) (by
      rw [SSet.yonedaEquiv_symm_comp, hz]
      exact hu.symm) (by
      rw [SSet.yonedaEquiv_symm_comp, ← Category.assoc, boundaryVertex_ι]
      exact hB₀.symm)
  have hcart : IsCocartesianCosliceVertex a p
      (SSet.yonedaEquiv (boundaryVertex n 0 ≫ C)) := by
    rw [hC₀, Equiv.apply_symm_apply]
    apply (hasCocartesianHornLifting_congr p (pointCosliceVertexEdge_ofEdge a e)).2
    exact he.hasCocartesianHornLifting p
  obtain ⟨D, hDC, hDp⟩ := exists_coslice_boundary_lift_of_cocartesian_vertex a p n C B hCp hcart
  refine ⟨D ≫ sliceUnderProjection a, ?_, ?_⟩
  · rw [← Category.assoc, hDC, hCu]
  · change D ≫ sliceUnderPostcomp a p ≫ sliceUnderProjection (a ≫ p) = b
    rw [← Category.assoc, hDp, hBp]

/-- 概要：相対始点境界充填条件はホモトピー圏で同型な頂点の間で保たれる。
方針：同型を実際の可逆辺で表し、辺による輸送を適用する。
規約：p は quasicategory 間の inner fibration。使われ方：普遍余錐の選択によらない輸送。 -/
lemma InitialBoundaryLifting.of_vertexIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {x y : X _⦋0⦌} (hx : InitialBoundaryLifting p x) (e : VertexIso x y) :
    InitialBoundaryLifting p y := by
  obtain ⟨f, hf⟩ := homotopyCategory_homMk_surjective x y e.hom
  have hi : IsInvertibleEdge f := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk f)
    rw [hf]
    infer_instance
  let f' : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (SSet.yonedaEquiv (SSet.yonedaEquiv.symm x)) y :=
    ⟨f.edge, f.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply x).symm, f.tgt_eq⟩
  have hi' : IsInvertibleEdge f' := (isInvertibleEdge_congr (e := f') (f := f) rfl).2 hi
  have hx' : InitialBoundaryLifting p (SSet.yonedaEquiv (SSet.yonedaEquiv.symm x)) :=
    (SSet.yonedaEquiv.apply_symm_apply x).symm ▸ hx
  exact InitialBoundaryLifting.of_invertibleEdge p (SSet.yonedaEquiv.symm x) hx' f' hi'

end SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects
