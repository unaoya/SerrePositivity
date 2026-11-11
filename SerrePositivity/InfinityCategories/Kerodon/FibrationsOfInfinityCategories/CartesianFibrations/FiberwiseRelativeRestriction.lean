module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomPostcomposition

/-!
概要：変動する添字の関手の全空間で、部分図式と標的の全図式を同時に固定する。
方針：添字の前合成と標的の後合成の可換四角形から引き戻しへの比較を作る。
規約：構成に fibration 性は仮定しない。
使われ方：相対 Kan の存在の組み立ての全空間の相対比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：部分図式と標的の全図式が一致する全空間の引き戻し。
方針：底 C 上の添字の射に関する前後合成を引き戻す。
規約：第一成分は D の部分図式、第二成分は E の全図式。
使われ方：変動する相対余錐の全空間の標的。 -/
abbrev FiberwiseRelativeTarget {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i)

/-- 概要：図式とその標的の像を同時に保つ全空間の相対比較。
方針：前合成と後合成の可換性で二成分を引き戻しへ合わせる。
規約：i と U は任意。
使われ方：相対 join 上の図式の普遍性の全空間での判定。 -/
def fiberwiseRelativeRestriction {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom L.hom D ⟶ FiberwiseRelativeTarget i U :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp L.hom U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPre_postcomp i U)

/-- 概要：相対比較の第一射影は部分図式への制限。
方針：引き戻しの持ち上げの第一射影を使う。
規約：全空間の射の等式。
使われ方：指定した元の図式の回収。 -/
lemma fiberwiseRelativeRestriction_fst {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) :
    fiberwiseRelativeRestriction i U ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i := pullback.lift_fst _ _ _

/-- 概要：相対比較の第二射影は標的への全図式の後合成。
方針：引き戻しの持ち上げの第二射影を使う。
規約：全図式の像を保つ。
使われ方：底での指定された図式の回収。 -/
lemma fiberwiseRelativeRestriction_snd {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) :
    fiberwiseRelativeRestriction i U ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp L.hom U := pullback.lift_snd _ _ _

/-- 概要：相対比較の標的から元の底 C への射影。
方針：部分図式の第一射影とその底への射影を合成する。
規約：もう一方の成分からの射影とも一致する。
使われ方：相対比較の各底頂点での fiber。 -/
def fiberwiseRelativeProjection {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) : FiberwiseRelativeTarget i U ⟶ C :=
  pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection K.hom D

/-- 概要：相対比較の標的の底射影は第二成分から計算しても同じ。
方針：引き戻し条件を底への射影へ後合成する。
規約：両成分は同じ底に載る。
使われ方：標的の fiber の引き戻し表示。 -/
lemma fiberwiseRelativeProjection_snd {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) :
    fiberwiseRelativeProjection i U =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom E := by
  have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection K.hom E)
    (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp K.hom U)
      (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i))
  simpa only [fiberwiseRelativeProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPostcomp_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPre_projection] using h

/-- 概要：全空間の相対比較は元の底を厳密に保つ。
方針：第一射影への合成と制限の底の保存を使う。
規約：標的の底射影は第一成分で定義したもの。
使われ方：fiber への相対比較の制限。 -/
lemma fiberwiseRelativeRestriction_projection {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) :
    fiberwiseRelativeRestriction i U ≫ fiberwiseRelativeProjection i U =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom D := by
  rw [fiberwiseRelativeProjection, ← Category.assoc,
    fiberwiseRelativeRestriction_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomPre_projection]

/-- 概要：全空間の相対比較を底の一頂点の fiber へ制限する。
方針：相対比較が底射影を保つ等式で fiber の射を誘導する。
規約：底の頂点は任意。
使われ方：通常の相対余錐制限との比較と局所充填条件の移送。 -/
def fiberwiseRelativeRestrictionFiber {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom D) c ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (fiberwiseRelativeProjection i U) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (fiberwiseRelativeRestriction i U)
    (fiberwiseRelativeRestriction_projection i U) c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
