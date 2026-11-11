module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFamilies

/-!
概要：始域 x を固定した comma の族と、y の図式・x→G(y) のホモトピーの全単射。
方針：comma の展開の始点を fiber の固定条件で揃え、持ち上げの両逆を計算する。
規約：G、添字 A、X、Y に充填性の仮定は不要。
使われ方：単位の普遍性を境界上の図式とホモトピーの延長に移す。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：固定始域の comma の族の Y 値の標的図式。
方針：fiber の包含に続けて標的射影を取る。
規約：始点 x は全パラメータで固定。
使われ方：族を図式とホモトピーの組に展開する。 -/
noncomputable def unitCommaFiberTarget {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) : A ⟶ Y :=
  (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G

/-- 概要：固定始域の comma の族が表す x→G(y) のホモトピー。
方針：comma のホモトピーの始点を fiber の定値条件で置き換える。
規約：ホモトピーの射自体は元の comma の族からのもの。
使われ方：相対的なホモトピーの延長問題の指定。 -/
noncomputable def unitCommaFiberHomotopy {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :
    SSet.Homotopy (SSet.const x) (unitCommaFiberTarget f ≫ G) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x)).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x)).h₀]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
    rfl
  h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x)).h₁
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：x→G∘b のホモトピーは始域 x の comma の族を定める。
方針：comma への持ち上げを始域射影の定値 fiber に制限する。
規約：b は任意の非定値の関手。
使われ方：図式とホモトピーの組から comma の族を回収する。 -/
noncomputable def unitCommaFiberCurry {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G (SSet.const x) b H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source _ _ _ _)

/-- 概要：固定始域へ持ち上げた族を comma に含めると元の持ち上げ。
方針：fiber の持ち上げの包含後の等式。
規約：厳密な等式。
使われ方：両逆と相対条件の計算。 -/
lemma unitCommaFiberCurry_ι {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) :
    unitCommaFiberCurry G x b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G (SSet.const x) b H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 概要：持ち上げた固定始域の族の標的は元の b。
方針：包含後の式と comma の標的の計算を使う。
規約：ホモトピーまでではなく厳密な等式。
使われ方：族の表示の全単射の逆則。 -/
lemma unitCommaFiberCurry_target {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) :
    unitCommaFiberTarget (unitCommaFiberCurry G x b H) = b := by
  rw [unitCommaFiberTarget, unitCommaFiberCurry_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target]

/-- 概要：持ち上げた固定始域の族の区間展開は元のホモトピー。
方針：包含後の式と comma の持ち上げの区間展開を使う。
規約：区間を第一因子へ交換した向き。
使われ方：ホモトピーの射の回収。 -/
lemma unitCommaFiberCurry_uncurry {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry (unitCommaFiberCurry G x b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x) =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h := by
  rw [unitCommaFiberCurry_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_uncurry]

/-- 概要：回収した族のホモトピーの射は元の H の射。
方針：二つの区間交換の合成を相殺する。
規約：端点の等式による輸送は射の値に影響しない。
使われ方：依存する図式とホモトピーの組の回収。 -/
lemma unitCommaFiberCurry_homotopy {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (b : A ⟶ Y) (H : SSet.Homotopy (SSet.const x) (b ≫ G)) :
    (unitCommaFiberHomotopy (unitCommaFiberCurry G x b H)).h = H.h := by
  change (β_ A (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry (unitCommaFiberCurry G x b H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x) = H.h
  rw [unitCommaFiberCurry_uncurry]
  have hc : (β_ A (Δ[1] : SSet.{u})).hom ≫ (β_ (Δ[1] : SSet.{u}) A).hom = 𝟙 _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  rw [← Category.assoc, hc, Category.id_comp]

/-- 概要：固定始域の comma の族を組へ展開して戻すと元の族。
方針：fiber の包含後に矢印と標的を比較する。
規約：図式 A の充填性は不要。
使われ方：族の表示の全単射の第一の逆則。 -/
lemma unitCommaFiberCurry_homotopyFamily {A X Y : SSet.{u}} {G : Y ⟶ X} {x : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) :
    unitCommaFiberCurry G x (unitCommaFiberTarget f) (unitCommaFiberHomotopy f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma_hom_ext
  · rw [unitCommaFiberCurry_uncurry]
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫
      ((β_ A (Δ[1] : SSet.{u})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x)) = _
    have hc : (β_ (Δ[1] : SSet.{u}) A).hom ≫ (β_ A (Δ[1] : SSet.{u})).hom = 𝟙 _ := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hc, Category.id_comp]
  · exact unitCommaFiberCurry_target G x _ _

/-- 概要：図式とホモトピーの依存する組は標的の等式とホモトピーの射で決まる。
方針：標的の等式を消去し、ホモトピーの外延性を使う。
規約：相対条件の証明は proof irrelevance で比較する。
使われ方：族の表示の全単射の第二の逆則。 -/
lemma unitCommaFiberDiagram_ext {A X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    {b c : A ⟶ Y} (hb : b = c)
    (H : SSet.Homotopy (SSet.const x) (b ≫ G))
    (K : SSet.Homotopy (SSet.const x) (c ≫ G)) (hH : H.h = K.h) :
    (⟨b, H⟩ : Σ b : A ⟶ Y, SSet.Homotopy (SSet.const x) (b ≫ G)) = ⟨c, K⟩ := by
  subst c
  have hk : H = K := SSet.RelativeMorphism.Homotopy.ext hH
  subst K
  rfl

/-- 概要：固定始域の comma の族と標的図式・ホモトピーの組の厳密な全単射。
方針：展開と fiber への持ち上げ、および両逆を組み合わせる。
規約：任意の単体集合 A、任意の G と頂点 x。
使われ方：始対象性のホーン延長問題を図式とホモトピーの延長に移す。 -/
noncomputable def unitCommaFiberFamilyEquiv {X Y : SSet.{u}} (G : Y ⟶ X) (x : X _⦋0⦌)
    (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) ≃ Σ b : A ⟶ Y, SSet.Homotopy (SSet.const x) (b ≫ G) where
  toFun f := ⟨unitCommaFiberTarget f, unitCommaFiberHomotopy f⟩
  invFun d := unitCommaFiberCurry G x d.1 d.2
  left_inv := unitCommaFiberCurry_homotopyFamily
  right_inv d := by
    obtain ⟨b, H⟩ := d
    exact unitCommaFiberDiagram_ext G x (unitCommaFiberCurry_target G x b H) _ _
      (unitCommaFiberCurry_homotopy G x b H)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
