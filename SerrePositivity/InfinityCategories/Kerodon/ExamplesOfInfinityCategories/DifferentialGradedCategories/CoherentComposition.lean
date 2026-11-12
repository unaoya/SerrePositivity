module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathCubeComposition

/-!
# coherent 単体の合成面と Alexander–Whitney 合成

概要：coherent 単体の Hom 写像は Path の合成を標準 Hom の AW 合成へ送る。
方針：豊穣関手の合成保存を単体ごとに評価し、座標1面の Path の分解を代入する。
規約：AW の第一引数は後の射、第二引数は前の射。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の合成項の計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {J : Type u} [LinearOrder J]

/-- 概要：coherent 単体の Path の合成の像は AW 合成に等しい。
方針：豊穣関手の map_comp を一対の Hom の単体で評価する。
規約：前の Path が f、後の Path が g。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面を成分族の AW 演算へ移す。 -/
lemma coherentHom_comp_apply
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    {a b c : J} {n : ℕ} (f : (nerve (Path a b)) _⦋n⦌)
    (g : (nerve (Path b c)) _⦋n⦌) :
    (s.map (.mk a) (.mk c)).app _ (f.prod' g ⋙ compFunctor (.mk a) (.mk b) (.mk c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((s.map (.mk b) (.mk c)).app _ g) ((s.map (.mk a) (.mk b)).app _ f) := by
  exact congrArg (fun φ ↦ φ.app (Opposite.op ⦋n⦌) (f, g))
    (s.map_comp (.mk a) (.mk b) (.mk c))

/-- 概要：coherent 単体の座標1面の像は左右の区間の像の AW 合成である。
方針：座標1面の Path の左右分解と、豊穣関手の合成保存を組み合わせる。
規約：左右の区間への制限は同じ残りの座標の単体から作る。
使われ方：HA 1.3.1.16 の立方体境界の合成面を AW の和へ展開する入口。 -/
lemma coherentCube_face_one_apply
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    {a b : J} (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (i : Fin (m + 1)) {n : ℕ}
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube (ULift.{u} (Fin m))) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
        ((s.map (.mk (e i).val.val) (.mk b)).app _
          ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor (e i).val.property.2 S)).app _
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ F)))
        ((s.map (.mk a) (.mk (e i).val.val)).app _
          ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor (e i).val.property.1 S)).app _
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ F))) := by
  let f := (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor (e i).val.property.1 S)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ F)
  let g := (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeIntervalFunctor (e i).val.property.2 S)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i false).app _ F)
  have h := congrArg (fun φ ↦ φ.app (Opposite.op ⦋n⦌) F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap_face_one hab e i)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ F) =
    f.prod' g ⋙ compFunctor (.mk a) (.mk (e i).val.val) (.mk b) at h
  change (s.map (.mk a) (.mk b)).app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeMap hab S).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFaceMap e i true).app _ F)) = _
  rw [h]
  exact coherentHom_comp_apply s f g

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
