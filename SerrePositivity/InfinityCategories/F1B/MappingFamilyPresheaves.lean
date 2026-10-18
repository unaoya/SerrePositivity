module

public import SerrePositivity.InfinityCategories.F1B.MappingFamilies

/-!
概要：非定値端点のホモトピー族の前層とその表現可能性。
方針：矢印空間の表示の全単射でパラメータの前合成を移す。
規約：各点の写像空間に限らず全端点図式を同時に保持する。
使われ方：自然な比較の型を前層の自然変換として指定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：F(a)→b の非定値端点のホモトピー族の前層。
方針：矢印空間の表示で任意のパラメータ射の前合成を移す。
規約：値は集合としての族の型。使われ方：自然な比較の始域。 -/
def leftMappingFamilyPresheaf {X Y : SSet.{u}} (F : X ⟶ Y) : SSet.{u}ᵒᵖ ⥤ Type u where
  obj A := LeftMappingFamily F A.unop
  map i := ↾fun f => leftMappingFamilyEquiv F _ (i.unop ≫ (leftMappingFamilyEquiv F _).symm f)
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
  obj A := RightMappingFamily G A.unop
  map i := ↾fun f => rightMappingFamilyEquiv G _ (i.unop ≫ (rightMappingFamilyEquiv G _).symm f)
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
    (i : A ⟶ B) (f : LeftMappingFamily F B) :
    ((leftMappingFamilyPresheaf F).map i.op f).homotopy.h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ f.homotopy.h := by
  change (leftMappingArrowHomotopy (i ≫ leftMappingArrowLift F f.source f.target f.homotopy)).h = _
  rw [leftMappingArrowHomotopy_precomp_h, leftMappingArrowLift_homotopy_h]

/-- 概要：右族のパラメータ作用は raw なホモトピーの前合成。
方針：comma の表示の前合成自然性と持ち上げの回収を使う。
規約：自然性に隠れたホモトピー類の選択はない。
使われ方：前層の自然性を実際の族の自然性として読む。 -/
lemma rightMappingFamilyPresheaf_map_h {A B X Y : SSet.{u}} (G : Y ⟶ X)
    (i : A ⟶ B) (f : RightMappingFamily G B) :
    ((rightMappingFamilyPresheaf G).map i.op f).homotopy.h =
      (i ▷ (Δ[1] : SSet.{u})) ≫ f.homotopy.h := by
  change (unitCommaHomotopy (i ≫ unitCommaLift G f.source f.target f.homotopy)).h = _
  rw [unitCommaHomotopy_precomp, unitCommaHomotopy_lift_h]

/-- 概要：左族の前層は矢印空間の表現可能前層と自然同型。
方針：族の表示の全単射を各パラメータで使う。
規約：パラメータに関する厳密な自然性。使われ方：自然比較の Yoneda 表示。 -/
def leftMappingFamilyPresheafIso {X Y : SSet.{u}} (F : X ⟶ Y) :
    yoneda.obj (leftMappingArrow F) ≅ leftMappingFamilyPresheaf F :=
  NatIso.ofComponents (fun A => (leftMappingFamilyEquiv F A.unop).toIso) (by
    intro A B i
    apply ConcreteCategory.hom_ext
    intro f
    change leftMappingFamilyEquiv F _ (i.unop ≫ f) =
      leftMappingFamilyEquiv F _ (i.unop ≫
        (leftMappingFamilyEquiv F _).symm (leftMappingFamilyEquiv F _ f))
    rw [Equiv.symm_apply_apply])

/-- 概要：右族の前層は comma 空間の表現可能前層と自然同型。
方針：族の表示の全単射を各パラメータで使う。
規約：パラメータに関する厳密な自然性。使われ方：自然比較の Yoneda 表示。 -/
def rightMappingFamilyPresheafIso {X Y : SSet.{u}} (G : Y ⟶ X) :
    yoneda.obj (unitComma G) ≅ rightMappingFamilyPresheaf G :=
  NatIso.ofComponents (fun A => (rightMappingFamilyEquiv G A.unop).toIso) (by
    intro A B i
    apply ConcreteCategory.hom_ext
    intro f
    change rightMappingFamilyEquiv G _ (i.unop ≫ f) =
      rightMappingFamilyEquiv G _ (i.unop ≫
        (rightMappingFamilyEquiv G _).symm (rightMappingFamilyEquiv G _ f))
    rw [Equiv.symm_apply_apply])

/-- 概要：左族の始域図式の自然な射影。
方針：族の source を取り出す。
規約：値域は X の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def leftMappingFamilySource {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingFamilyPresheaf F ⟶ yoneda.obj X where
  app _ := ↾LeftMappingFamily.source
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ leftMappingArrowLift F f.source f.target f.homotopy) ≫
      leftMappingArrowSource F = i.unop ≫ f.source
    rw [Category.assoc, leftMappingArrowLift_source]

/-- 概要：左族の標的図式の自然な射影。
方針：族の target を取り出す。
規約：値域は Y の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def leftMappingFamilyTarget {X Y : SSet.{u}} (F : X ⟶ Y) :
    leftMappingFamilyPresheaf F ⟶ yoneda.obj Y where
  app _ := ↾LeftMappingFamily.target
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ leftMappingArrowLift F f.source f.target f.homotopy) ≫
      leftMappingArrowTarget F = i.unop ≫ f.target
    rw [Category.assoc, leftMappingArrowLift_target]

/-- 概要：右族の始域図式の自然な射影。
方針：族の source を取り出す。
規約：値域は X の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def rightMappingFamilySource {X Y : SSet.{u}} (G : Y ⟶ X) :
    rightMappingFamilyPresheaf G ⟶ yoneda.obj X where
  app _ := ↾RightMappingFamily.source
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ unitCommaLift G f.source f.target f.homotopy) ≫
      unitCommaSource G = i.unop ≫ f.source
    rw [Category.assoc, unitCommaLift_source]

/-- 概要：右族の標的図式の自然な射影。
方針：族の target を取り出す。
規約：値域は Y の表現可能前層。使われ方：端点を保つ自然比較の条件。 -/
def rightMappingFamilyTarget {X Y : SSet.{u}} (G : Y ⟶ X) :
    rightMappingFamilyPresheaf G ⟶ yoneda.obj Y where
  app _ := ↾RightMappingFamily.target
  naturality {_ _} i := by
    apply ConcreteCategory.hom_ext
    intro f
    change (i.unop ≫ unitCommaLift G f.source f.target f.homotopy) ≫
      unitCommaTarget G = i.unop ≫ f.target
    rw [Category.assoc, unitCommaLift_target]

end SerrePositivity.InfinityCategories
