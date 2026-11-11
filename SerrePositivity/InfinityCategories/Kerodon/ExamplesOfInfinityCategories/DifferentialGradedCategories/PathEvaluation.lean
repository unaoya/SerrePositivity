module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathNerve
public import Mathlib.Data.Fin.Rev

/-!
# coherent 単体の Path の立方体の評価

概要：選んだ有限内部点集合の立方体を native Path の nerve に送り、豊穣関手を通じて評価する。
方針：内部点の部分集合に端点を付加し、その nerve の写像を Hom の豊穣写像と合成する。
規約：立方体の向きには内部点の降順の番号付けを使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の各高次成分の候補。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：有限線形順序集合を最大点から最小点へ番号付けする。
方針：昇順の順序同型に Fin の順序反転を前合成する。
規約：置換符号の基準となる座標の順序。
使われ方：HA 1.3.1.16 の立方体の向きを dg nerve の削除符号と合わせる。 -/
def descendingEnumeration {A : Type u} [LinearOrder A] (S : Finset A) : Fin S.card ≃ S :=
  Fin.revPerm.trans (S.orderIsoOfFin rfl).toEquiv

/-- 概要：内部点の部分集合を端点付きの Path に送る関手。
方針：有限内部点の集合から開区間への像を取り、端点を加える。
規約：包含方向に進む native な Path の圏を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の有限内部点の立方体の包含。 -/
def pathCubeFunctor {J : Type u} [LinearOrder J] {a b : J} (hab : a < b)
    (S : Finset (Set.Ioo a b)) : Set ↥S ⥤ Path a b :=
  (show Monotone (fun U : Set ↥S ↦ (Subtype.val : ↥S → Set.Ioo a b) '' U) from
    fun _ _ h ↦ Set.image_mono h).functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathOfInteriorFunctor hab

/-- 概要：有限内部点の立方体を Path の Hom 単体集合へ送る。
方針：端点付加の関手の nerve を取る。
規約：立方体の座標が 1 ならその内部点を Path に含める。
使われ方：HA 1.3.1.16 の coherent 単体の立方体の Hom 写像。 -/
def pathCubeMap {J : Type u} [LinearOrder J] {a b : J} (hab : a < b)
    (S : Finset (Set.Ioo a b)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube ↥S ⟶ nerve (Path a b) :=
  nerveMap (pathCubeFunctor hab S)

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：coherent 単体の豊穣 Hom 写像を有限内部点の立方体へ制限する。
方針：Path への立方体の写像と豊穣関手の Hom 写像を合成する。
規約：係数環と Path の宇宙を u でそろえる。
使われ方：HA 1.3.1.16 の立方体の基本鎖の評価の入力。 -/
def coherentCubeHom {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube ↥S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) (s.obj (.mk a)) (s.obj (.mk b)) :=
  pathCubeMap hab S ≫ s.map (.mk a) (.mk b)

/-- 概要：coherent 単体の選んだ Path の有限内部点に対応する斉次成分を取る。
方針：内部点を降順に番号付けし、全最大旗の符号付き和を Hom へ送る。
規約：内部点数 m に対して cochain 次数は −m。
使われ方：HA 1.3.1.16 の dg nerve の成分の候補。 -/
def coherentCubeComponent {J : Type u} [LinearOrder J]
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    {a b : J} (hab : a < b) (S : Finset (Set.Ioo a b)) :
    GradedHom R (s.obj (.mk a)) (s.obj (.mk b)) (-(S.card : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation (R := R) (D := D) (descendingEnumeration S) (coherentCubeHom s hab S)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
