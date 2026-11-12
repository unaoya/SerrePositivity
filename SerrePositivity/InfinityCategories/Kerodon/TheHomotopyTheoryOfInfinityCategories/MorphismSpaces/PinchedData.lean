module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedReconstructFaces

/-! # 方程式を課す前の右 pinched データ

概要：先頭面と終端を固定した単体データをまとめ、線形族の回収と再構成を共通に扱う。
方針：単体方程式を構造体に入れず、先頭面の等式から成分計算を取り出す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：逆構成の方程式の循環しない証明。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (x y : D)

/-- 概要：先頭面が x の定値データで最終対象が y の単体データ。
方針：方程式を課す前のデータに二つの端点条件だけを添える。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形化と逆構成の共通の計算対象。 -/
structure Data (n : ℕ) where
  /-- 元の単体データ。 -/
  val : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 1)
  /-- 先頭面全体は始点の定値データ。 -/
  source : val.pullback Fin.castSuccOrderEmb.toOrderHom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData
  /-- 最終対象は終点。 -/
  target : val.obj (Fin.last (n + 1)) = y

namespace Data

variable {A D x y}

/-- 概要：方程式を課す前でも全先頭対象は x。
方針：先頭面の等式を対象で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形成分の対象の移送。 -/
lemma source_obj {n : ℕ} (s : Data A D x y n) (i : Fin (n + 1)) : s.val.obj i.castSucc = x :=
  congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n => t.obj i) s.source

/-- 概要：方程式を課す前でも最終対象は y。
方針：構造体の終端条件を取り出す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：終端成分の対象の移送。 -/
lemma target_obj {n : ℕ} (s : Data A D x y n) : s.val.obj (Fin.last (n + 1)) = y := s.target

/-- 概要：右 pinched データから全終端成分を線形族として読む。
方針：共通のデータ回収操作に両端の対象の等式を渡す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：逆構成の方程式の線形化。 -/
def toLinearData {n : ℕ} (s : Data A D x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n :=
  s.val.toPinchedLinearData x y (source_obj s) (target_obj s)

/-- 概要：データから回収した成分は元の終端成分と異種等号で一致する。
方針：共通の回収操作の成分の比較を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：微分と削除・切断の成分の比較。 -/
lemma toLinearData_component_heq {n : ℕ} (s : Data A D x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    HEq ((toLinearData s).component J k hJ hk)
      (s.val.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (J.min' hJ).castSucc (Fin.last (n + 1)) k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withLast hJ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _)
        (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withLast]; omega)) :=
  s.val.toPinchedLinearData_component_heq x y (source_obj s) (target_obj s) J k hJ hk

/-- 概要：実際の右 pinched 単体から方程式を忘れたデータを得る。
方針：データ部分を取り、先頭面の等式をデータへ写す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：既存の順写像との比較。 -/
def ofSimplex {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) : Data A D x y n where
  val := s.val.toSimplexData
  source := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData s.source
  target := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.target_obj s

/-- 概要：実際の単体の方程式を忘れてから回収しても線形族は変わらない。
方針：同じ回収操作の定義を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：元の順写像とデータの計算の接続。 -/
lemma toLinearData_ofSimplex {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) _⦋n⦌) :
    toLinearData (ofSimplex s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData s := rfl

end Data

namespace LinearData

variable {A D x y}

/-- 概要：線形族から先頭面と終端を固定した右 pinched データを再構成する。
方針：既存の再構成データに、その先頭面と終端の計算を添える。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形解からの実際の単体の逆構成。 -/
def toData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) : Data A D x y n where
  val := f.toSimplexData
  source := f.toSimplexData_front
  target := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj_of_eq_last x y rfl

/-- 概要：再構成した右 pinched データを読むと元の線形族に戻る。
方針：再構成データの成分の片側の逆則を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形方程式を元の単体方程式へ戻す。 -/
lemma toLinearData_toData {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) : Data.toLinearData f.toData = f :=
  f.toSimplexData_toPinchedLinearData

end LinearData

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
