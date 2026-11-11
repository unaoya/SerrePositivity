module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ModelBifibrantFrame
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：元の全 Hom 単体と bifibrant DK frame の固定終域の矢を厳密に同定する。
方針：元の次数と射の up・down、全部分圏の包みを明示的に往復する。
規約：元の解像・射・全作用素を保持する。
使われ方：同じ source frame の弱比較を実 right Kan 屋根比較へ送る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory Opposite
open HomotopicalAlgebra _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (X Y : BifibrantObject C) (q : CofibrantResolution (C := C) simplex X.obj)

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
abbrev modelBifibrantSourceFrameElementCategory :=
  ULiftHom.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj).Elements)ᵒᵖ)

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
def modelBifibrantSourceFrameElementsToDK : modelBifibrantSourceFrameElementCategory X Y q ⥤
    CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) where
  obj s := by
    let t : ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj).Elementsᵒᵖ :=
      ULiftHom.objDown s
    exact
      { left := ⟨t.unop.obj.unop⟩
        right := ⟨⟨⟩⟩
        hom := ⟨ObjectProperty.homMk t.unop.val⟩ }
  map f := by
    let a := ULift.down f
    exact CostructuredArrow.homMk ⟨a.unop.hom.unop⟩ (by
      apply ULift.ext
      apply ObjectProperty.hom_ext
      exact a.unop.map_val)

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
def modelBifibrantSourceFrameDKToElements :
    CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) ⥤
        modelBifibrantSourceFrameElementCategory X Y q where
  obj s := ULiftHom.objUp (op (Functor.elementsMk _ (op (ULift.down s.left))
    (ULift.down s.hom).hom))
  map {s t} f := ⟨Quiver.Hom.op
    { hom := (ULift.down f.left).op
      map_val := by
        exact congrArg (fun g : (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q).obj s.left ⟶
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) =>
            (ULift.down g).hom) (CostructuredArrow.w f) }⟩

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
def modelBifibrantSourceFrameElementsDKEquivalence :
  modelBifibrantSourceFrameElementCategory X Y q ≌
    CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y) where
  functor := modelBifibrantSourceFrameElementsToDK X Y q
  inverse := modelBifibrantSourceFrameDKToElements X Y q
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
lemma modelBifibrantSourceFrameElementsToDK_degree (s :
  modelBifibrantSourceFrameElementCategory X Y q) :
    ULift.down ((modelBifibrantSourceFrameElementsToDK X Y q).obj s).left =
      (show ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj).Elementsᵒᵖ from
        ULiftHom.objDown s).unop.obj.unop := rfl

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
lemma modelBifibrantSourceFrameElementsToDK_arrow (s :
  modelBifibrantSourceFrameElementCategory X Y q) :
    (ULift.down ((modelBifibrantSourceFrameElementsToDK X Y q).obj s).hom).hom =
      (show ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj).obj Y.obj).Elementsᵒᵖ from
        ULiftHom.objDown s).unop.val := rfl

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
lemma modelBifibrantSourceFrameElementsToDK_inverse : modelBifibrantSourceFrameElementsToDK X Y q ⋙
    modelBifibrantSourceFrameDKToElements X Y q =
      𝟭 (modelBifibrantSourceFrameElementCategory X Y q) := rfl

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
lemma modelBifibrantSourceFrameDKToElements_inverse : modelBifibrantSourceFrameDKToElements X Y q ⋙
    modelBifibrantSourceFrameElementsToDK X Y q = 𝟭 _ := rfl

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
def modelBifibrantSourceFrameElementDegree : modelBifibrantSourceFrameElementCategory X Y q ⥤
    AsSmall.{max u v} SimplexCategory where
  obj s := ⟨(ULiftHom.objDown s).unop.obj.unop⟩
  map f := ⟨(ULift.down f).unop.hom.unop⟩

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
def modelBifibrantSourceFrameElementsDKNerveIso :
  nerve (modelBifibrantSourceFrameElementCategory X Y q) ≅
    nerve (CostructuredArrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantDKFrame X q)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantObject C Y)) where
  hom := { app _ := ↾fun σ => σ ⋙ modelBifibrantSourceFrameElementsToDK X Y q
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ modelBifibrantSourceFrameDKToElements X Y q
           naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 概要：同じ bifibrant frame の全単体・次数・射の表示を厳密に回収する。
方針：元の次数の up・down と全部分圏の射の包みの往復を評価する。
規約：元の実関手・全作用素を保持。使われ方：実屋根の次数比較への接続。 -/
def modelBifibrantSourceFrameElementDegreeNerve :
  nerve (modelBifibrantSourceFrameElementCategory X Y q) ⟶
    nerve (AsSmall.{max u v} SimplexCategory) where
  app _ := ↾fun σ => σ ⋙ modelBifibrantSourceFrameElementDegree X Y q
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
