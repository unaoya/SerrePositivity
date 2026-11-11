module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
概要：定値係数の weighted nerve の評価と、終対象での係数値への評価。
方針：重みの図式の最後の成分を取り、終対象への射による係数の自然変換と合成する。
規約：係数の Kan 性は不要で、構成は単体集合の射として自然性を満たす。
使われ方：Kerodon §5.3.3（Tag 025W）、底の標準単体上の相対ホーンを最後の係数値へ送る操作。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：単調写像は最後の初区間への制限に続く包含として表せる。
方針：全初区間の包含が恒等となることを初区間の分解式に適用する。
規約：最後の頂点の像は標的の最後の頂点とは限らない。
使われ方：Kerodon §5.3.3（Tag 025W）、最後の係数値の評価の自然性。 -/
lemma simplexPrefixRestriction_last_factor {m n : SimplexCategory} (α : m ⟶ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α (Fin.last m.len) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion
        (α.toOrderHom (Fin.last m.len)).val n.len
        (Nat.le_of_lt_succ (α.toOrderHom (Fin.last m.len)).isLt) = α := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion m.len m.len _ ≫ α = α
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, Category.id_comp]

/-- 概要：定値係数の weighted nerve を最後の成分で係数の値へ評価する。
方針：初区間の図式の自然性を使い、最後の成分の評価が面・退化と可換であることを示す。
規約：底の圏は任意で、定値係数 K は任意の単体集合。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve のホーンから係数値のホーンを得る射。 -/
def weightedNerveConstantEvaluation (C : Type u) [Category.{u} C] (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve ((CategoryTheory.Functor.const C).obj K) ⟶ K where
  app d := ↾fun s ↦ SSet.yonedaEquiv (s.2.app (Fin.last d.unop.len))
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨σ, τ⟩
    change SSet.yonedaEquiv (stdSimplex.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop (Fin.last e.unop.len)) ≫
          τ.app (α.unop.toOrderHom (Fin.last e.unop.len))) =
      K.map α (SSet.yonedaEquiv (τ.app (Fin.last d.unop.len)))
    have ht := τ.naturality (homOfLE (Fin.le_last
      (α.unop.toOrderHom (Fin.last e.unop.len))))
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion
        (α.unop.toOrderHom (Fin.last e.unop.len)).val d.unop.len _) ≫
        τ.app (Fin.last d.unop.len) =
      τ.app (α.unop.toOrderHom (Fin.last e.unop.len)) ≫ 𝟙 K at ht
    have ht' := ht.trans (Category.comp_id (τ.app
      (α.unop.toOrderHom (Fin.last e.unop.len))))
    have hn : K.map α (SSet.yonedaEquiv (τ.app (Fin.last d.unop.len))) =
        SSet.yonedaEquiv (stdSimplex.map α.unop ≫ τ.app (Fin.last d.unop.len)) :=
      SSet.yonedaEquiv_naturality α.unop (τ.app (Fin.last d.unop.len))
    rw [hn]
    apply congrArg SSet.yonedaEquiv
    rw [← ht', ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      simplexPrefixRestriction_last_factor]

/-- 概要：終対象を持つ底の係数図式から終対象の値への定値図式への自然変換。
方針：各対象から終対象への一意な射を係数関手で写す。
規約：底の終対象は通常の圏の終対象。
使われ方：Kerodon §5.3.3（Tag 025W）、標準単体の最後の係数値への評価。 -/
def weightedNerveTerminalCoefficient {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t) :
    F ⟶ (CategoryTheory.Functor.const C).obj (F.obj t) where
  app c := F.map (ht.from c)
  naturality c d f := by
    change F.map f ≫ F.map (ht.from d) = F.map (ht.from c) ≫ 𝟙 _
    rw [Category.comp_id, ← CategoryTheory.Functor.map_comp]
    exact congrArg F.map (ht.hom_ext _ _)

/-- 概要：終対象を持つ圏の weighted nerve を終対象における係数値へ評価する。
方針：終対象への係数の自然変換を weighted nerve に写し、定値係数を評価する。
規約：これは底の射影を忘れた全空間からの単体集合の射。
使われ方：Kerodon §5.3.3（Tag 025W）、底の単体上のホーンを最後の Kan 複体へ移す操作。 -/
def weightedNerveTerminalEvaluation {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {t : C} (ht : IsTerminal t) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F ⟶ F.obj t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (weightedNerveTerminalCoefficient F ht) ≫
    weightedNerveConstantEvaluation C (F.obj t)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
