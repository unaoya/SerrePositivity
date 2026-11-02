module
public import SerrePositivity.InfinityCategories.Derived.DGModuleSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
/-!
概要：全 dg 自然なホモトピー同値による終点後合成は同じ四角形の余極限性を保つ。
方針：指定後合成の coslice 辺を可逆とし、同じ全余錐の比較へ送る。
規約：通常の加群同型を仮定せず、元の二胞体を保持する。
使われ方：分裂 cone 射影から元の零ホモトピー四角形への cofiber 性の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DGModuleSquareData
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {W X Y Z T : ModuleCategory A D}

lemma isPushout_postcompose_of_homotopy (s : DGModuleSquareData A D W X Y Z)
    (q : Z ⟶ T) (hq : IsIso ((moduleToHomotopy A D).map q))
    (hs : IsPushoutSquare s.square) : IsPushoutSquare (s.postcompose q).square := by
  have := dgModuleEdge_isIso_of_homotopy A D q hq
  have he : IsInvertibleEdge (X := dgModuleNerve A D) (dgModuleEdge A D q).toTruncated :=
    (edgeToPathHomotopyCategory _).map_isIso
      (SSet.Truncated.HomotopyCategory₂.homMk (dgModuleEdge A D q).toTruncated)
  have hp := (isInvertibleEdge_congr (X := dgModuleNerve A D)
    (s.postcomposeSliceEdge_projection q)).mpr he
  have hi := leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (pushoutSpan s.square)) (s.postcomposeSliceEdge q) hp
  have hc : IsColimitCone (s.postcomposeCocone q) :=
    hs.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk
      (s.postcomposeSliceEdge q)))
  exact (F2.isColimitCone_iff_of_cocone_val_eq (s.postcomposeCocone q)
    (pushoutCocone (s.postcompose q).square) rfl).mp hc

end SerrePositivity.InfinityCategories.DGModuleSquareData
