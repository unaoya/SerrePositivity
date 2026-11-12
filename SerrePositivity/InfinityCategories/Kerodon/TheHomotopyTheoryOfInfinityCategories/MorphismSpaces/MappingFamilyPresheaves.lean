module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingFamilies

/-!
概要：非定値端点のホモトピー族の前層とその表現可能性。
方針：矢印空間の表示の全単射でパラメータの前合成を移す。
規約：各点の写像空間に限らず全端点図式を同時に保持する。
使われ方：自然な比較の型を前層の自然変換として指定する。

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

/-- 概要：F(a)→b の非定値端点のホモトピー族の前層。
方針：矢印空間の表示で任意のパラメータ射の前合成を移す。
規約：値は集合としての族の型。使われ方：自然な比較の始域。 -/
def leftMappingFamilyPresheaf {X Y : SSet.{u}} (F : X ⟶ Y) : SSet.{u}ᵒᵖ ⥤ Type u where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingFamily F A.unop
  map i := ↾fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F _ (i.unop ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F _).symm f)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro f
    simp
  map_comp i j := by
    apply ConcreteCategory.hom_ext
    intro f
    simp [Category.assoc]

/-- 概要：a→G(b) の非定値端点のホモトピー族の前層。
方針：comma 空間の表示で任意のパラメータ射の前合成を移す。
規約：値は集合としての族の型。使われ方：自然な比較の値域。 -/
def rightMappingFamilyPresheaf {X Y : SSet.{u}} (G : Y ⟶ X) : SSet.{u}ᵒᵖ ⥤ Type u where
  obj A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightMappingFamily G A.unop
  map i := ↾fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G _ (i.unop ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G _).symm f)
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro f
    simp
  map_comp i j := by
    apply ConcreteCategory.hom_ext
    intro f
    simp [Category.assoc]

/-- 概要：左族のパラメータ作用は raw なホモトピーの前合成。
方針：矢印の表示の前合成自然性と持ち上げの回収を使う。
規約：自然性に隠れたホモトピー類の選択はない。
使われ方：前層の自然性を実際の族の自然性として読む。 -/
lemma leftMappingFamilyPresheaf_map_h {A B X Y : SSet.{u}} (F : X ⟶ Y)
    (i : A ⟶ B) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingFamily F B) :
    ((leftMappingFamilyPresheaf F).map i.op f).homotopy.h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ f.homotopy.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F f.source f.target f.homotopy)).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowHomotopy_precomp_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_homotopy_h]

/-- 概要：右族のパラメータ作用は raw なホモトピーの前合成。
方針：comma の表示の前合成自然性と持ち上げの回収を使う。
規約：自然性に隠れたホモトピー類の選択はない。
使われ方：前層の自然性を実際の族の自然性として読む。 -/
lemma rightMappingFamilyPresheaf_map_h {A B X Y : SSet.{u}} (G : Y ⟶ X)
    (i : A ⟶ B) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightMappingFamily G B) :
    ((rightMappingFamilyPresheaf G).map i.op f).homotopy.h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ f.homotopy.h := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy (i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G f.source f.target f.homotopy)).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaHomotopy_lift_h]

/-- 概要：左族の前層は矢印空間の表現可能前層と自然同型。
方針：族の表示の全単射を各パラメータで使う。
規約：パラメータに関する厳密な自然性。使われ方：自然比較の Yoneda 表示。 -/
def leftMappingFamilyPresheafIso {X Y : SSet.{u}} (F : X ⟶ Y) :
    yoneda.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrow F) ≅ leftMappingFamilyPresheaf F :=
  NatIso.ofComponents (fun A => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F A.unop).toIso) (by
    intro A B i
    apply ConcreteCategory.hom_ext
    intro f
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F _ (i.unop ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F _ (i.unop ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingFamilyEquiv F _ f))
    rw [Equiv.symm_apply_apply])

/-- 概要：右族の前層は comma 空間の表現可能前層と自然同型。
方針：族の表示の全単射を各パラメータで使う。
規約：パラメータに関する厳密な自然性。使われ方：自然比較の Yoneda 表示。 -/
def rightMappingFamilyPresheafIso {X Y : SSet.{u}} (G : Y ⟶ X) :
    yoneda.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitComma G) ≅ rightMappingFamilyPresheaf G :=
  NatIso.ofComponents (fun A => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G A.unop).toIso) (by
    intro A B i
    apply ConcreteCategory.hom_ext
    intro f
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G _ (i.unop ≫ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G _ (i.unop ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingFamilyEquiv G _ f))
    rw [Equiv.symm_apply_apply])

/-- 概要：左族の始域図式の自然な射影。
方針：族の source を取り出す。
規約：値域は X の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def leftMappingFamilySource {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingFamilyPresheaf F ⟶ yoneda.obj X where
  app _ := ↾_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingFamily.source
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F f.source f.target f.homotopy) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowSource F = i.unop ≫ f.source
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_source]

/-- 概要：左族の標的図式の自然な射影。
方針：族の target を取り出す。
規約：値域は Y の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def leftMappingFamilyTarget {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingFamilyPresheaf F ⟶ yoneda.obj Y where
  app _ := ↾_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftMappingFamily.target
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift F f.source f.target f.homotopy) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowTarget F = i.unop ≫ f.target
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingArrowLift_target]

/-- 概要：右族の始域図式の自然な射影。
方針：族の source を取り出す。
規約：値域は X の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def rightMappingFamilySource {X Y : SSet.{u}} (G : Y ⟶ X) :
    rightMappingFamilyPresheaf G ⟶ yoneda.obj X where
  app _ := ↾_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightMappingFamily.source
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G f.source f.target f.homotopy) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G = i.unop ≫ f.source
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_source]

/-- 概要：右族の標的図式の自然な射影。
方針：族の target を取り出す。
規約：値域は Y の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def rightMappingFamilyTarget {X Y : SSet.{u}} (G : Y ⟶ X) :
    rightMappingFamilyPresheaf G ⟶ yoneda.obj Y where
  app _ := ↾_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightMappingFamily.target
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift G f.source f.target f.homotopy) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaTarget G = i.unop ≫ f.target
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaLift_target]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
