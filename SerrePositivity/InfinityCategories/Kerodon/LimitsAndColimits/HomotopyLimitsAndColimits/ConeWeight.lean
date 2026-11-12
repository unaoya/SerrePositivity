module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedTowerTrivialFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
概要：Bousfield–Kan の重みと定値の点を受け入れる補助重み。
方針：各 over 圏に始対象を付加し、その nerve を取る。
規約：点側の制限と元の重み側の制限を区別する。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の strict 極限の標準比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：小圏に始対象を付加する操作の厳密な通常の関手。
方針：既存の WithInitial.map を用い、恒等と合成は対象と射の場合分けで確認する。
規約：Cat の対象と Hom は同じ宇宙。
使われ方：Kerodon 7.5.3（Tag 03AP） の自然な補助重み。 -/
def initialExtensionFunctor : Cat.{u, u} ⥤ Cat.{u, u} where
  obj C := Cat.of (WithInitial C)
  map F := (WithInitial.map F.toFunctor).toCatHom
  map_id C := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      cases X <;> rfl
    · intro X Y f
      cases X <;> cases Y <;> try exact PEmpty.elim f
      all_goals
        simp only [Cat.of_α, Cat.Hom.id_toFunctor, Functor.toCatHom_toFunctor,
          WithInitial.map_obj, Functor.id_obj, WithInitial.map_map, eqToHom_refl,
          Functor.id_map, WithInitial.down, Category.comp_id, Category.id_comp]
      all_goals exact Subsingleton.elim _ _
  map_comp F G := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro X
      cases X <;> rfl
    · intro X Y f
      cases X <;> cases Y <;> try exact PEmpty.elim f
      all_goals simp [WithInitial.map, WithInitial.down]

variable {I : Type u} [SmallCategory I]

/-- 概要：各 over 圏に始対象を加えた nerve の重み。
方針：over、始対象の付加、nerve の三関手を合成する。
規約：V(i) = N(WithInitial(I/i))。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の標準比較を二つの重みの制限で扱う。 -/
def bousfieldKanConeWeight (I : Type u) [SmallCategory I] : I ⥤ SSet.{u} :=
  Over.mapFunctor I ⋙ initialExtensionFunctor ⋙ nerveFunctor

/-- 概要：元の over 圏の包含による Bousfield–Kan 重みから補助重みへの射。
方針：WithInitial.incl の nerve を各成分に取る。
規約：始対象の頂点を選ぶ射とは異なる。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の κ 側の制限。 -/
def bousfieldKanConeWeightInclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ bousfieldKanConeWeight I where
  app i := nerveMap WithInitial.incl
  naturality i j f := by
    change nerveMap (Over.map f) ≫ nerveMap WithInitial.incl =
      nerveMap WithInitial.incl ≫ nerveMap (WithInitial.map (Over.map f))
    rfl

/-- 概要：付加した始対象の頂点による定値一点重みから補助重みへの射。
方針：各成分に新しい始対象の nervePoint を取る。
規約：点は Δ[0] で、全ての遷移で新しい始対象を保つ。
使われ方：Kerodon 7.5.3（Tag 03AP） の strict 極限側の重みの制限。 -/
def bousfieldKanConeWeightPoint :
    (Functor.const I).obj (Δ[0] : SSet.{u}) ⟶ bousfieldKanConeWeight I where
  app i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (WithInitial.star : WithInitial (Over i))
  naturality i j f := by
    change (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint WithInitial.star =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint WithInitial.star ≫ nerveMap (WithInitial.map (Over.map f))
    rw [Category.id_comp]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change ComposableArrows.mk₀ (WithInitial.star : WithInitial (Over j)) =
      (nerveMap (WithInitial.map (Over.map f))).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ (WithInitial.star : WithInitial (Over i)))
    exact (nerveMap_app_mk₀ (WithInitial.map (Over.map f))
      (WithInitial.star : WithInitial (Over i))).symm

/-- 概要：定値の点から補助重みへの射の全成分は anodyne。
方針：始対象の頂点包含の left anodyne 性を Kan fibration の持ち上げに適用する。
規約：添字圏 I には制限を置かない。
使われ方：Kerodon 7.5.3（Tag 03AP）、塔の end の点側の制限の同値性。 -/
lemma bousfieldKanConeWeightPoint_anodyne (i : I) :
    anodyneExtensions (bousfieldKanConeWeightPoint.app i) := by
  intro E B p hp
  have : Fibration p := ⟨hp⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne (WithInitial.starInitial (C := Over i)) p _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem

/-- 概要：fibration の塔の補助重みの end から一点重みの end への制限は trivial Kan fibration。
方針：始対象の頂点包含の成分ごとの anodyne 性を重みの制限の定理へ渡す。
規約：零段の Kan 性と隣接遷移の Fibration 性を前提とする。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の標準比較の一点側。 -/
lemma bousfieldKanConeWeightPoint_tower_trivialKanFibration
    (H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre bousfieldKanConeWeightPoint H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsPre_tower_trivialKanFibration bousfieldKanConeWeightPoint
    bousfieldKanConeWeightPoint_anodyne

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
