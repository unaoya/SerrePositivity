module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinEndpointComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor

/-!
概要：join の両端図式の射と、通常の join および fat join への包含の自然性。
方針：次数ごとの直和の各因子で射を定義し、左右の包含の自然性を使う。
規約：空の因子も許し、quasicategory 性は要求しない。
使われ方：Kerodon §4.6.6（Tag 04HY）、両端を固定した図式の部分族への制限。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：左因子を両端図式へ含める。
方針：各次数で直和の左の包含を使う。
規約：左右の因子は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定左端の条件を回収する射。 -/
def joinEndpointInl (A B : SSet.{u}) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram A B where
  app _ := ↾Sum.inl
  naturality _ _ _ := rfl

/-- 概要：右因子を両端図式へ含める。
方針：各次数で直和の右の包含を使う。
規約：左右の因子は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定右端の条件を回収する射。 -/
def joinEndpointInr (A B : SSet.{u}) : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram A B where
  app _ := ↾Sum.inr
  naturality _ _ _ := rfl

/-- 概要：両端図式の左包含に続く通常の join への包含は join の左包含。
方針：各次数で定義を計算する。
規約：射の等式として成立する。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定図式の左端への制限。 -/
lemma joinEndpointInl_inclusion (A B : SSet.{u}) :
    joinEndpointInl A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion A B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B := rfl

/-- 概要：両端図式の右包含に続く通常の join への包含は join の右包含。
方針：各次数で定義を計算する。
規約：射の等式として成立する。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定図式の右端への制限。 -/
lemma joinEndpointInr_inclusion (A B : SSet.{u}) :
    joinEndpointInr A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion A B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B := rfl

/-- 概要：両端図式の左包含に続く fat join への包含は fat join の左包含。
方針：各次数で定義を計算する。
規約：射の等式として成立する。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join の固定左端への制限。 -/
lemma joinEndpointInl_fatInclusion (A B : SSet.{u}) :
    joinEndpointInl A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion A B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B := rfl

/-- 概要：両端図式の右包含に続く fat join への包含は fat join の右包含。
方針：各次数で定義を計算する。
規約：射の等式として成立する。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join の固定右端への制限。 -/
lemma joinEndpointInr_fatInclusion (A B : SSet.{u}) :
    joinEndpointInr A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion A B = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B := rfl

/-- 概要：両端図式を二つの射で写す。
方針：各次数の直和に Sum.map を適用する。
規約：左右の因子を保つ。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定端点のパラメータの変更。 -/
def joinEndpointMap {A B C D : SSet.{u}} (f : A ⟶ C) (g : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram C D where
  app d := ↾Sum.map (f.app d) (g.app d)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a => exact congrArg Sum.inl (ConcreteCategory.congr_hom (f.naturality α) a)
    | inr b => exact congrArg Sum.inr (ConcreteCategory.congr_hom (g.naturality α) b)

/-- 概要：左右の射を両端図式上にまとめる。
方針：次数ごとの直和からの射を場合分けで作る。
規約：左右の図式に交わりの整合条件は不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、join の両端に指定する図式。 -/
def joinEndpointDesc {A B X : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram A B ⟶ X where
  app d := ↾Sum.elim (f.app d) (g.app d)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    cases s with
    | inl a => exact ConcreteCategory.congr_hom (f.naturality α) a
    | inr b => exact ConcreteCategory.congr_hom (g.naturality α) b

/-- 概要：両端図式の包含は通常の join の射と可換。
方針：直和の各場合で join の左右の包含の自然性を使う。
規約：四つの因子は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、通常の join 図式の制限の可換四角形。 -/
lemma joinEndpointInclusion_map {A B C D : SSet.{u}} (f : A ⟶ C) (g : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f g =
      joinEndpointMap f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion C D := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  cases s with
  | inl a =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap f g) d) a
  | inr b =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap f g) d) b

/-- 概要：両端図式の包含は fat join の射と可換。
方針：直和の各場合で fat join の左右の包含の自然性を使う。
規約：四つの因子は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、fat join 図式の制限の可換四角形。 -/
lemma fatJoinEndpointInclusion_map {A B C D : SSet.{u}} (f : A ⟶ C) (g : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinMap f g =
      joinEndpointMap f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion C D := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  cases s with
  | inl a =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_map f g) d) a
  | inr b =>
    exact ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_map f g) d) b

/-- 概要：両端図式の貼り合わせは前合成を各因子に移せる。
方針：直和の二つの場合で定義を計算する。
規約：射の等式として成立する。
使われ方：Kerodon §4.6.6（Tag 04HY）、部分族における固定図式の同定。 -/
lemma joinEndpointMap_desc {A B C D X : SSet.{u}}
    (f : A ⟶ C) (g : B ⟶ D) (p : C ⟶ X) (q : D ⟶ X) :
    joinEndpointMap f g ≫ joinEndpointDesc p q = joinEndpointDesc (f ≫ p) (g ≫ q) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  cases s <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
