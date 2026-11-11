module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialNerveCut

/-!
概要：WithInitial の新しい始対象を含まない部分の射列を元の圏に復元する。
方針：対象と射を構成子で戻し、恒等・合成と包含後の移送の等式を確認する。
規約：元の圏の非空性を仮定せず、復元に対象の選択を使わない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と点の join の同定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：WithInitial の新しい始対象でない対象を元の圏に戻す。
方針：対象の場合分けを行い、始対象の場合は非一致の証明から排除する。
規約：元の圏の非空性や対象の選択は要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveOldObj (x : WithInitial C) (h : x ≠ .star) : C := by
  cases x with
  | of x => exact x
  | star => exact (h rfl).elim
omit [SmallCategory C] in
/-- 概要：元の圏へ戻した対象の包含は元の対象と一致する。
方針：対象の構成子で計算する。
規約：始対象でないことの証明の選択には依存しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveOldObj_of (x : WithInitial C) (h : x ≠ .star) :
    WithInitial.of (initialNerveOldObj x h) = x := by
  cases x with
  | of x => rfl
  | star => exact (h rfl).elim
/-- 概要：新しい始対象を端点に持たない射を元の圏の射に戻す。
方針：元の対象の間の射がそのまま元の圏の射であることを使う。
規約：両端が新しい始対象でないことを要求する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveOldMap {x y : WithInitial C} (hx : x ≠ .star) (hy : y ≠ .star)
    (f : x ⟶ y) : initialNerveOldObj x hx ⟶ initialNerveOldObj y hy := by
  cases x with
  | star => exact (hx rfl).elim
  | of x =>
    cases y with
    | star => exact (hy rfl).elim
    | of y => exact f
/-- 概要：元の圏への射の復元は恒等射を保つ。
方針：元の対象の構成子で恒等射を計算する。
規約：対象の非一致の証明は固定する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveOldMap_id (x : WithInitial C) (h : x ≠ .star) :
    initialNerveOldMap h h (𝟙 x) = 𝟙 (initialNerveOldObj x h) := by
  cases x with
  | of x => rfl
  | star => exact (h rfl).elim
/-- 概要：元の圏への射の復元は合成を保つ。
方針：三つの端点を元の対象に帰着し、WithInitial の合成の定義を使う。
規約：三つの端点が新しい始対象でないことを要求する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveOldMap_comp {x y z : WithInitial C}
    (hx : x ≠ .star) (hy : y ≠ .star) (hz : z ≠ .star) (f : x ⟶ y) (g : y ⟶ z) :
    initialNerveOldMap hx hz (f ≫ g) =
      initialNerveOldMap hx hy f ≫ initialNerveOldMap hy hz g := by
  cases x with
  | star => exact (hx rfl).elim
  | of x =>
    cases y with
    | star => exact (hy rfl).elim
    | of y =>
      cases z with
      | star => exact (hz rfl).elim
      | of z => rfl
/-- 概要：復元した射の包含は端点の等式による移送を介して元の射に一致する。
方針：元の対象の場合分けで等式の移送を計算する。
規約：端点の等式を eqToHom で明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveOldMap_of {x y : WithInitial C} (hx : x ≠ .star) (hy : y ≠ .star)
    (f : x ⟶ y) :
    eqToHom (initialNerveOldObj_of x hx) ≫ f =
      (WithInitial.incl : C ⥤ WithInitial C).map (initialNerveOldMap hx hy f) ≫
        eqToHom (initialNerveOldObj_of y hy) := by
  cases x with
  | star => exact (hx rfl).elim
  | of x =>
    cases y with
    | star => exact (hy rfl).elim
    | of y =>
      simp only [initialNerveOldMap, initialNerveOldObj, WithInitial.incl,
        eqToHom_refl, Category.id_comp, Category.comp_id]
/-- 概要：全ての対象が新しい始対象でない関手を元の圏へ戻す。
方針：対象と射を復元し、恒等射と合成の計算を使う。
規約：始域の対象と Hom の宇宙は係数の宇宙とは独立。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveOldFunctor {J : Type v} [Category.{w} J]
    (F : J ⥤ WithInitial C) (h : ∀ i, F.obj i ≠ .star) : J ⥤ C where
  obj i := initialNerveOldObj (F.obj i) (h i)
  map {i j} f := initialNerveOldMap (h i) (h j) (F.map f)
  map_id i := by rw [F.map_id, initialNerveOldMap_id]
  map_comp f g := by rw [F.map_comp, initialNerveOldMap_comp]
/-- 概要：元の圏へ戻した関手の対象の包含は元の関手の対象と一致する。
方針：対象の復元の等式を各成分に適用する。
規約：実際の対象の等式で表す。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveOldFunctor_obj {J : Type v} [Category.{w} J]
    (F : J ⥤ WithInitial C) (h : ∀ i, F.obj i ≠ .star) (i : J) :
    WithInitial.of ((initialNerveOldFunctor F h).obj i) = F.obj i := initialNerveOldObj_of _ _
/-- 概要：元の圏へ戻した関手の射は元の射と端点の等式の移送を介して一致する。
方針：射の復元の移送の式を各射に適用する。
規約：包含の後の合成の順序は元の圏の通常の合成順序。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveOldFunctor_map {J : Type v} [Category.{w} J]
    (F : J ⥤ WithInitial C) (h : ∀ i, F.obj i ≠ .star) {i j : J} (f : i ⟶ j) :
    eqToHom (initialNerveOldFunctor_obj F h i) ≫ F.map f =
      (WithInitial.incl : C ⥤ WithInitial C).map ((initialNerveOldFunctor F h).map f) ≫
        eqToHom (initialNerveOldFunctor_obj F h j) := initialNerveOldMap_of _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
