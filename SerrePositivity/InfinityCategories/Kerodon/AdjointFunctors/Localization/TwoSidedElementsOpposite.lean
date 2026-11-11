module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements

/-!
# 元の二方向要素圏と右ラベルの要素圏上の反対要素圏

概要：底・左ラベル・右ラベルを、右ラベルの対象と左ラベルへ厳密に並べ替える。
方針：元の左の反変条件と右の共変条件を同じ二つの要素圏の射条件に使う。
規約：元の全対象・全射を保持する厳密な往復を構成する。
使われ方：重み付き左 bar と反対側の元の一方向 bar の同型。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite

variable {W : Type u} [Category.{u} W] (A : Wᵒᵖ ⥤ Type u) (S : W ⥤ Type u)

abbrev oppositeElements := (((Functor.Elements.π S).op ⋙ A).Elements)ᵒᵖ

def baseElement (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S) : S.Elements := S.elementsMk X.base X.right

def baseElementMap {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S} (f : X ⟶ Y) : baseElement A S X ⟶ baseElement A S Y :=
  Functor.Elements.homMk f.base f.right

def toOpposite : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S ⥤ oppositeElements A S where
  obj X := op (((Functor.Elements.π S).op ⋙ A).elementsMk (op (baseElement A S X)) X.left)
  map {X Y} f := Quiver.Hom.op (show
      (((Functor.Elements.π S).op ⋙ A).elementsMk (op (baseElement A S Y)) Y.left) ⟶
      (((Functor.Elements.π S).op ⋙ A).elementsMk (op (baseElement A S X)) X.left) from
    Functor.Elements.homMk (baseElementMap A S f).op f.left)
  map_id _ := rfl
  map_comp _ _ := rfl

def fromOpposite : oppositeElements A S ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S where
  obj X := ⟨X.unop.obj.unop.obj, X.unop.val, X.unop.obj.unop.val⟩
  map f := ⟨f.unop.hom.unop.hom, f.unop.map_val, f.unop.hom.unop.map_val⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def oppositeEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element A S ≌ oppositeElements A S where
  functor := toOpposite A S
  inverse := fromOpposite A S
  unitIso := Iso.refl _
  counitIso := Iso.refl _

lemma toOpposite_naturality {B : Wᵒᵖ ⥤ Type u} (α : A ⟶ B) :
    toOpposite A S ⋙ (Functor.whiskerLeft (Functor.Elements.π S).op α).mapElements.op =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map α (𝟙 S) ⋙ toOpposite B S := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
