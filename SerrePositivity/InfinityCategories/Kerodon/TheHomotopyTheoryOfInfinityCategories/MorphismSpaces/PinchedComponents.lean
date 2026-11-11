module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedReadData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedIndex

/-! # 右 pinched 単体からの全斉次成分の回収

概要：右 pinched 単体の最終頂点を含む成分を二対象の間の線形成分族として取り出す。
方針：先頭面と最終点の固定条件で対象を同定し、集合の濃度で次数を合わせる。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形表示への順写像のデータ部分。
このデータの回収だけでは線形削除方程式の保存を主張しない。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：右 pinched 単体の全先頭頂点の対象は始点 x。
方針：先頭面全体の定値条件を各対象で評価する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：回収する成分の始点の移送。 -/
lemma source_obj {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) (i : Fin (n + 1)) :
    s.val.obj i.castSucc = x :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n => t.obj i) s.source

/-- 概要：右 pinched 単体の最終頂点の対象は終点 y。
方針：最終点の固定条件を零単体の対象で評価する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：回収する成分の終点の移送。 -/
lemma target_obj {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    s.val.obj (Fin.last (n + 1)) = y :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0 => t.obj 0) s.target

/-- 概要：右 pinched 単体の最終点を含む全成分を線形成分族として回収する。
方針：J に最終点を加えた集合の成分を取り、両端の対象だけを等式で移送する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：全次数の線形表示への順写像のデータ。 -/
def toLinearData {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n :=
  s.val.toSimplexData.toPinchedLinearData x y (source_obj s) (target_obj s)

/-- 概要：回収した各成分は元の最終点を含む成分と異種等号で一致する。
方針：対象の等式による cast を異種等号で除く。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：回収した成分の微分と合成の計算。 -/
lemma toLinearData_component_heq {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((toLinearData s).component J k hJ hk)
      (s.val.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega)) := by
  exact cast_heq _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
