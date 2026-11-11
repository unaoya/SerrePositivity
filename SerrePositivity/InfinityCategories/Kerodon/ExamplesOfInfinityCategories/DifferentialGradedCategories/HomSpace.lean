module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinearPullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.UniverseKan

/-!
# Dold–Kan Hom の小さい線形模型

概要：N4 の線形解を係数環の宇宙に収まる単体的加群とし、右 pinched Hom と比較する。
方針：線形引き戻しを使い、宇宙を持ち上げた後に N4 の全次数の同値を自然同型にする。
規約：このファイルだけでは豊穣合成や Mathlib の Γ との同型を主張しない。
使われ方：HA 1.3.1.12–1.3.1.14、Kerodon 2.5.6（Tag 00QQ）・2.5.9（Tag 00SC） の単体的 Hom の構成。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory SerrePositivity.DifferentialGraded
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories



variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：N4 の線形解の小さい単体的 R 加群を構成する。
方針：各次数の線形解と全ての単調写像に沿う線形引き戻しを取る。
規約：値の宇宙は u とし、対象の宇宙 v は独立に保つ。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の Dold–Kan Hom の成分模型。 -/
def homModule (x y : D) : SimplicialObject (ModuleCat.{u} R) where
  obj n := ModuleCat.of R (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R x y n.unop.len)
  map f := ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback f.unop.toOrderHom)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback_id s
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback_comp g.unop.toOrderHom f.unop.toOrderHom s).symm

/-- 概要：小さい線形単体的 Hom の台単体集合を取る。
方針：単体的加群の後に忘却関手を合成する。
規約：N4 の f 座標を用い、標準 chain map 座標との符号変更は別途実装する。
使われ方：HA 1.3.1.13、Kerodon 2.5.9.2（Tag 00SE） の豊穣 Hom の台。 -/
def homSpace (x y : D) : SSet.{u} := homModule (R := R) x y ⋙ forget (ModuleCat.{u} R)

/-- 概要：宇宙を持ち上げた小さい Hom は dg nerve の右 pinched Hom と同型である。
方針：N4 の線形成分回収と再構成を各次数で用い、引き戻しとの自然性を確認する。
規約：両辺を SSet の同じ宇宙 max u v で比較する。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の Hom の直接の線形充填の移送。 -/
def homSpaceLiftIso (x y : D) :
    SSet.uliftFunctor.{v, u}.obj (homSpace (R := R) x y) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y where
  hom :=
    { app := fun n ↦ ↾fun s ↦ s.down.toPinched
      naturality := by
        intro m n α
        apply ConcreteCategory.hom_ext
        intro s
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n.unop.len).injective
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback α.unop.toOrderHom s.down).toPinched) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (s.down.toPinched.pullback α.unop)
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched] }
  inv :=
    { app := fun n ↦ ↾fun s ↦ ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s)
      naturality := by
        intro m n α
        apply ConcreteCategory.hom_ext
        intro s
        apply ULift.ext
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback s α.unop }
  hom_inv_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_toPinched s.down
  inv_hom_id := by
    apply CategoryTheory.NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toPinched_toLinearSimplex s

open SSet.modelCategoryQuillen in
/-- 概要：持ち上げた小さい Hom は Kan 複体である。
方針：N4 の直接の線形充填による Kan 性を自然同型に沿って移す。
規約：一般の単体的群の Kan 定理は使わない。
使われ方：HA 1.3.1.14、Kerodon 2.5.9.2（Tag 00SE） の局所 Kan 性の準備。 -/
instance homSpaceLiftKan (x y : D) :
    SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj (homSpace (R := R) x y)) :=
  HomotopicalAlgebra.isFibrant_of_fibration (homSpaceLiftIso (R := R) x y).hom

/-- 概要：小さい Hom 自身が Kan 複体である。
方針：持ち上げた Hom の Kan 性から宇宙の持ち上げの反映性を使う。
規約：対象の宇宙を係数環の宇宙以下とする仮定はない。
使われ方：HA 1.3.1.14、Kerodon 2.5.9.2（Tag 00SE） の単体的豊穣化の局所 Kan 性。 -/
instance homSpaceKan (x y : D) : SSet.KanComplex (homSpace (R := R) x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.kanComplex_of_ulift.{v} (homSpace (R := R) x y)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
