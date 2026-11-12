module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison

/-!
概要：非定値端点を持つ矢印の族をホモトピーのデータとして表す。
方針：始域・標的・raw なホモトピーを保持し、矢印空間の表現可能性を証明する。
規約：quasicategory 性や各点での同値性は不要。
使われ方：B1 の自然な族の比較を通常の前層の自然変換として述べる。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：F(a)→b のパラメータ A 上のホモトピー族。
方針：二つの端点図式とその間のホモトピーを保持する。
規約：端点図式は非定値でよい。使われ方：写像空間の族の前層。 -/
structure LeftMappingFamily {X Y : SSet.{u}} (F : X ⟶ Y) (A : SSet.{u}) where
  source : A ⟶ X
  target : A ⟶ Y
  homotopy : SSet.Homotopy (source ≫ F) target

/-- 概要：a→G(b) のパラメータ A 上のホモトピー族。
方針：二つの端点図式とその間のホモトピーを保持する。
規約：端点図式は非定値でよい。使われ方：比較の値域の前層。 -/
structure RightMappingFamily {X Y : SSet.{u}} (G : Y ⟶ X) (A : SSet.{u}) where
  source : A ⟶ X
  target : A ⟶ Y
  homotopy : SSet.Homotopy source (target ≫ G)

/-- 概要：左族は両端と raw なホモトピーの一致で等しい。
方針：端点の等式を消去しホモトピーの外延性を使う。
規約：証明の選択は proof irrelevance で消す。使われ方：表現可能性の両逆。 -/
lemma LeftMappingFamily.ext_raw {A X Y : SSet.{u}} {F : X ⟶ Y}
    {f g : LeftMappingFamily F A} (hs : f.source = g.source) (ht : f.target = g.target)
    (hh : f.homotopy.h = g.homotopy.h) : f = g := by
  cases f with | mk a b H =>
    cases g with | mk a' b' H' =>
      dsimp at hs ht hh
      subst a' b'
      have hH : H = H' := RelativeMorphism.Homotopy.ext hh
      subst H'
      rfl

/-- 概要：右族は両端と raw なホモトピーの一致で等しい。
方針：端点の等式を消去しホモトピーの外延性を使う。
規約：証明の選択は proof irrelevance で消す。使われ方：表現可能性の両逆。 -/
lemma RightMappingFamily.ext_raw {A X Y : SSet.{u}} {G : Y ⟶ X}
    {f g : RightMappingFamily G A} (hs : f.source = g.source) (ht : f.target = g.target)
    (hh : f.homotopy.h = g.homotopy.h) : f = g := by
  cases f with | mk a b H =>
    cases g with | mk a' b' H' =>
      dsimp at hs ht hh
      subst a' b'
      have hH : H = H' := RelativeMorphism.Homotopy.ext hh
      subst H'
      rfl

/-- 概要：左族の前層は F(x)→y の矢印空間で表現される。
方針：両端とホモトピーの表示および持ち上げの厳密な両逆を使う。
規約：パラメータ A は任意。使われ方：自然な比較の Yoneda 表示。 -/
def leftMappingFamilyEquiv {X Y : SSet.{u}} (F : X ⟶ Y) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F) ≃ LeftMappingFamily F A where
  toFun f := ⟨f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F, f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy f⟩
  invFun f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F f.source f.target f.homotopy
  left_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy
  right_inv f := by
    apply LeftMappingFamily.ext_raw
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source _ _ _ _
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target _ _ _ _
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy_h _ _ _ _

/-- 概要：右族の前層は G の comma 空間で表現される。
方針：両端とホモトピーの表示および持ち上げの厳密な両逆を使う。
規約：パラメータ A は任意。使われ方：自然な比較の Yoneda 表示。 -/
def rightMappingFamilyEquiv {X Y : SSet.{u}} (G : Y ⟶ X) (A : SSet.{u}) :
    (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) ≃ RightMappingFamily G A where
  toFun f := ⟨f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G, f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy f⟩
  invFun f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G f.source f.target f.homotopy
  left_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_homotopy
  right_inv f := by
    apply RightMappingFamily.ext_raw
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source _ _ _ _
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target _ _ _ _
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
