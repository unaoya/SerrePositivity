module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitComma

/-!
概要：comma 値の図式を端点とホモトピーの族として展開し回収する。
方針：区間の境界の引き戻しの普遍性と curry・uncurry の両逆を使う。
規約：始域の図式 A は任意。端点の関手を定値に制限しない。
使われ方：固定始域の comma の始対象条件を相対ホモトピーの延長問題へ移す。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：comma の族を区間とパラメータの積からの射へ展開する。
方針：矢印の射影を uncurry する。
規約：区間が第一因子。
使われ方：comma の充填を X 内の図式の充填で計算する。 -/
noncomputable def unitCommaUncurry {A X Y : SSet.{u}} {G : Y ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) : (Δ[1] : SSet.{u}) ⊗ A ⟶ X :=
  uncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrow G)

/-- 概要：展開した comma の族の境界は始域と G を続けた標的。
方針：引き戻しの可換条件を uncurry し、境界図式の自然性を使う。
規約：二つの端点の関手をそのまま保つ。
使われ方：族のホモトピーの端点の計算。 -/
lemma unitCommaUncurry_boundary {A X Y : SSet.{u}} {G : Y ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    (boundary 1).ι ▷ A ≫ unitCommaUncurry f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) ((f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) ≫ G) := by
  unfold unitCommaUncurry
  rw [← uncurry_pre_app, Category.assoc]
  change uncurry (f ≫ (pullback.fst _ _ ≫ (pre (boundary 1).ι).app X)) = _
  rw [pullback.condition, ← Category.assoc, uncurry_natural_left]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaBoundary, uncurry_curry]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_naturality]
  rfl

/-- 概要：展開した comma の族の始点は始域射影。
方針：境界の零端点への制限。
規約：任意のパラメータ A。
使われ方：始域を固定した fiber の条件の認識。 -/
lemma unitCommaUncurry_zero {A X Y : SSet.{u}} {G : Y ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ unitCommaUncurry f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0 A, Category.assoc, unitCommaUncurry_boundary,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_zero]

/-- 概要：展開した comma の族の終点は標的射影の後の G。
方針：境界の一端点への制限。
規約：標的への関手は Y 値。
使われ方：指定された G の像の図式との比較。 -/
lemma unitCommaUncurry_one {A X Y : SSet.{u}} {G : Y ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ unitCommaUncurry f = (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) ≫ G := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1 A, Category.assoc, unitCommaUncurry_boundary,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_one]

/-- 概要：comma の族は始域図式から G を続けた標的図式へのホモトピーを与える。
方針：区間を第二因子へ交換し、二つの端点条件を使う。
規約：可逆なホモトピーには制限しない。
使われ方：comma の族を非定値の自然変換として扱う。 -/
noncomputable def unitCommaHomotopy {A X Y : SSet.{u}} {G : Y ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) ((f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) ≫ G) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ unitCommaUncurry f
  h₀ := by
    rw [← Category.assoc]
    exact unitCommaUncurry_zero f
  h₁ := by
    rw [← Category.assoc]
    exact unitCommaUncurry_one f
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：comma への持ち上げを展開すると元のホモトピーに戻る。
方針：矢印射影の計算と curry の往復を使う。
規約：ここでは区間を第一因子に置く。
使われ方：固定始域の族の回収の逆則。 -/
lemma unitCommaLift_uncurry {A X Y : SSet.{u}} (G : Y ⟶ X)
    (a : A ⟶ X) (b : A ⟶ Y) (H : SSet.Homotopy a (b ≫ G)) :
    unitCommaUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G a b H) = (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h := by
  unfold unitCommaUncurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_arrow, uncurry_curry]

/-- 概要：展開した comma の族は前合成に自然。
方針：uncurry のパラメータ自然性を使う。
規約：i は任意の単体集合の射。
使われ方：境界・ホーン上の族の制限。 -/
lemma unitCommaUncurry_precomp {A B X Y : SSet.{u}} {G : Y ⟶ X}
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    unitCommaUncurry (i ≫ f) = (Δ[1] ◁ i) ≫ unitCommaUncurry f := by
  unfold unitCommaUncurry
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：comma の族のホモトピーはパラメータ前合成に自然。
方針：展開の前合成自然性と区間交換の自然性を使う。
規約：標準の区間は第二因子。
使われ方：相対ホモトピーの延長条件。 -/
lemma unitCommaHomotopy_precomp {A B X Y : SSet.{u}} {G : Y ⟶ X}
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    (unitCommaHomotopy (i ≫ f)).h = (i ▷ (Δ[1] : SSet.{u})) ≫ (unitCommaHomotopy f).h := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ _ = _
  rw [unitCommaUncurry_precomp]
  have hc : (β_ A (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ i) =
      (i ▷ (Δ[1] : SSet.{u})) ≫ (β_ B (Δ[1] : SSet.{u})).hom := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.assoc]
  rfl

/-- 概要：comma の族は矢印の族と Y 値の標的から決まる。
方針：矢印の始点から X 値の射影を回収し、引き戻しの両射影で比較する。
規約：G に忠実性や充填性を仮定しない。
使われ方：ホモトピーの延長から comma の図式の延長を認識する。 -/
lemma unitComma_hom_ext {A X Y : SSet.{u}} {G : Y ⟶ X} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G}
    (hH : unitCommaUncurry f = unitCommaUncurry g)
    (hb : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) : f = g := by
  have ha : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G := by
    rw [← unitCommaUncurry_zero f, ← unitCommaUncurry_zero g, hH]
  apply pullback.hom_ext
  · exact uncurry_injective hH
  · apply CartesianMonoidalCategory.hom_ext
    · exact ha
    · exact hb

/-- 概要：comma の族をホモトピーへ展開して持ち上げると元の族。
方針：標的と矢印の両射影を計算する。
規約：射として厳密に回収する。
使われ方：固定始域の族の表示の両逆。 -/
lemma unitCommaLift_homotopy {A X Y : SSet.{u}} {G : Y ⟶ X}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G) (unitCommaHomotopy f) = f := by
  apply unitComma_hom_ext
  · rw [unitCommaLift_uncurry]
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫
      ((β_ A (Δ[1] : SSet.{u})).hom ≫ unitCommaUncurry f) = _
    have hc : (β_ (Δ[1] : SSet.{u}) A).hom ≫ (β_ A (Δ[1] : SSet.{u})).hom = 𝟙 _ := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hc, Category.id_comp]
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
