module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCosliceComparison

/-!
概要：左 cone の最小点の座標と反対圏の右 Hom の最大点の座標を比較する。
方針：path の全頂点を Fin.rev で反転し、正頂点の最小元を前終点の最大元へ移す。
規約：path の包含の向きは保ち、両端点の順序を交換する。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の実際の fiber 比較と左 Hom 比較の同定。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：初点から正頂点への path を頂点の反転で右 Hom の path にする。
方針：部分集合を Fin.rev の像にし、元の終点を始点、元の初点を終点にする。
規約：始点 j.succ は j.rev.castSucc へ、零は最後の頂点へ写る。
使われ方：Kerodon §4.6.7（Tag 01LA） の左最小点と右最大点の座標の同定。 -/
def reflectedFirstPath {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    Path (ULift.up j.rev.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := (fun k : ULift.{u} (Fin (n + 2)) ↦ ULift.up k.down.rev) '' P.I
  left := ⟨ULift.up j.succ, P.right, ULift.ext (Fin.rev_succ j)⟩
  right := ⟨ULift.up 0, P.left, ULift.ext (Fin.rev_zero _)⟩
  left_le k hk := by
    rcases hk with ⟨l, hl, rfl⟩
    change j.rev.castSucc ≤ l.down.rev
    rw [← Fin.rev_succ]
    exact Fin.rev_le_rev.mpr (P.le_right l hl)
  le_right k _ := Fin.le_last k.down

/-- 概要：反転した path の前終点の所属は元の正頂点の所属と同値。
方針：Fin.rev の二回の反転が恒等になることを使って像の原像を計算する。
規約：前終点 k.castSucc は元の k.rev.succ に対応する。
使われ方：Kerodon §4.6.7（Tag 01LA） の最小点と最大点の比較。 -/
lemma reflectedFirstPath_mem {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ))
    (k : Fin (n + 1)) :
    ULift.up k.castSucc ∈ (reflectedFirstPath P).I ↔ ULift.up k.rev.succ ∈ P.I := by
  constructor
  · rintro ⟨l, hl, he⟩
    have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) ↦ a.down.rev) he
    change l.down.rev.rev = k.castSucc.rev at he'
    rw [Fin.rev_rev, Fin.rev_castSucc] at he'
    have hl' : l = ULift.up k.rev.succ := ULift.ext he'
    rwa [hl'] at hl
  · intro hk
    refine ⟨ULift.up k.rev.succ, hk, ?_⟩
    apply ULift.ext
    change k.rev.succ.rev = k.castSucc
    rw [Fin.rev_succ, Fin.rev_rev]

/-- 概要：反転した path の最大の前終点は元の最初の正頂点の反転。
方針：最大元の上界性と最小元の下界性を所属の対応で移す。
規約：値はどちらも Fin(n+1) の添字。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の fiber 比較の実際の座標の一致。 -/
lemma reflectedFirstPath_maximum {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (reflectedFirstPath P) = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum P).rev := by
  apply le_antisymm
  · apply Fin.rev_le_rev.mp
    rw [Fin.rev_rev]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_le P
    exact (reflectedFirstPath_mem P _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem (reflectedFirstPath P))
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum
    apply (reflectedFirstPath_mem P _).mpr
    rw [Fin.rev_rev]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum_mem P

/-- 概要：path の頂点の反転は包含圏の関手を与える。
方針：包含を部分集合の像の包含へ写す。
規約：両端点は正規化した右 Hom の端点。
使われ方：Kerodon §4.6.7（Tag 01LA） の実際の Hom の座標射の比較。 -/
def reflectedFirstPathFunctor {n : ℕ} (j : Fin (n + 1)) :
    Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) ⥤
      Path (ULift.up j.rev.castSucc : ULift.{u} (Fin (n + 2)))
        (ULift.up (Fin.last (n + 1))) where
  obj := reflectedFirstPath
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 概要：反転した path の最大点の射は各頂点で元の最小点の反転を返す。
方針：最大点の射の評価式と最小点の反転の式を合成する。
規約：入力の simplex の次数は任意。
使われ方：Kerodon §4.6.7（Tag 01LA） の fiber 比較の豊穣 Hom の成分計算。 -/
lemma reflectedFirstPathMaximumMap_apply {n : ℕ} (j : Fin (n + 1))
    {d : SimplexCategoryᵒᵖ}
    (F : (nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2)))
      (ULift.up j.succ))).obj d) (k : Fin (d.unop.len + 1)) :
    (SimplexCategory.Hom.toOrderHom
      (((nerveMap (reflectedFirstPathFunctor j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j.rev).app d F).down)) k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimum (F.obj k)).rev := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j.rev).app d
    (F ⋙ reflectedFirstPathFunctor j)).down.toOrderHom k = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply]
  exact reflectedFirstPath_maximum (F.obj k)


/-- 概要：左最小点の座標を標準単体の反転で戻すと右最大点の座標になる。
方針：各 simplex の各頂点で最小点と最大点の反転の式を使う。
規約：終点までの初区間の包含と全体の標準単体の反転を明示する。
使われ方：Kerodon §4.6.7（Tag 01LA） の一定の底の上の比較射の同定。 -/
lemma reflectedFirstPathMaximumMap {n : ℕ} (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap.{u} j ≫
      SSet.opFunctor.map (stdSimplex.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt))) ≫
      (stdSimplex.opIso ⦋n⦌).hom =
    nerveMap (reflectedFirstPathFunctor j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j.rev := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro F
  apply stdSimplex.ext
  intro k
  change (stdSimplex.opObjEquiv.{u, u}
    ((SSet.opFunctor.map (stdSimplex.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)))).app
        (Opposite.op ⦋d⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j).app (Opposite.op ⦋d⦌) F))) k = _
  rw [stdSimplex.opObjEquiv_apply]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)).toOrderHom
    ((SSet.opObjEquiv
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j).app (Opposite.op ⦋d⦌) F)).down.toOrderHom k.rev)).rev = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap_apply, Fin.rev_rev]
  exact (reflectedFirstPathMaximumMap_apply j F k).symm

/-- 概要：反転した空間の simplex の Yoneda 射を反転して戻すと標準単体の反転で表せる。
方針：各次数で標準単体の反転と反転関手の定義を評価する。
規約：X の Kan 性は要求しない。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の fiber の係数の評価。 -/
lemma reflectedYonedaMap {X : SSet.{u}} {n : ℕ} (s : X.op _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm s) =
      (stdSimplex.opIso ⦋n⦌).hom ≫ SSet.yonedaEquiv.symm (SSet.opObjEquiv s) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：一定の底の上の係数評価は反転した path の標準右 Hom の座標に一致する。
方針：係数の初区間への制限を反転し、最小点と最大点の射の比較を使う。
規約：反転した係数の n 単体 s を固定する。
使われ方：HTT 4.2.4.1 の実際の fiber 比較と既存の Hom 比較の同定。 -/
lemma reflectedConstantCoefficient {X : SSet.{u}} {n : ℕ}
    (s : X.op _⦋n⦌) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
        SSet.yonedaEquiv.symm s) =
    nerveMap (reflectedFirstPathFunctor j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap j.rev ≫
      SSet.yonedaEquiv.symm (SSet.opObjEquiv s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_pre, reflectedYonedaMap]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ SSet.yonedaEquiv.symm (SSet.opObjEquiv s))
    (reflectedFirstPathMaximumMap j)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
