module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoofPostcompose
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofPrecomposeHomotopy

/-!
# 元の frame 比較による roof の始域自然性

概要：元の始域射を持つ frame の比較を四列ホモトピーへ代入する。
方針：同じ要素圏の射影から両 frame と全 augmentation を引き戻す。
規約：元の全単体・元の始域射・同じ frame を保持する。
使われ方：既存 Map^h の比較の始域自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.SerrePositivity.HomotopyFunctionComplex
open _root_.SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X' X Y : C} (A' A : SimplexCategory ⥤ C)
  (p' : A' ⟶ (Functor.const SimplexCategory).obj X') (hp' : ∀ n, W (p'.app n))
  (p : A ⟶ (Functor.const SimplexCategory).obj X) (hp : ∀ n, W (p.app n))
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a)) (α : A' ⟶ A) (f : X' ⟶ X)
  (hα : α ≫ p = p' ≫ (Functor.const SimplexCategory).map f)

def frameSpanSourceIndexMap :
    ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤
      ULiftHom.{max u v} (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A').obj Y).Elements)ᵒᵖ :=
  ULiftHom.down.{0, v, max u v} ⋙ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y).mapElements.op ⋙ ULiftHom.up

include hα in
lemma frameLeftRoofColimitMap_precompose :
    AnodyneHomotopy.anodyneQ.map
        (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap A' A α) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap W A' p' hp' hA') =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap W A p hp hA) ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y) := by
  let I := (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y).Elements)ᵒᵖ
  let K : I ⥤ SimplexCategory := (Functor.Elements.π ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).leftOp
  let U' := K ⋙ A'
  let U := K ⋙ A
  let q' : U' ⟶ (Functor.const I).obj X' := Functor.whiskerLeft K p'
  let q : U ⟶ (Functor.const I).obj X := Functor.whiskerLeft K p
  let β : U' ⟶ U := Functor.whiskerLeft K α
  let σ : U ⟶ (Functor.const I).obj Y :=
    { app s := s.unop.val
      naturality s t a := by
        change A.map a.unop.hom.unop ≫ t.unop.val = s.unop.val ≫ 𝟙 Y
        exact a.unop.map_val.trans (Category.comp_id _).symm }
  have he : β ≫ q = q' ≫ (Functor.const I).map f := by
    apply NatTrans.ext
    funext s
    exact NatTrans.congr_app hα (K.obj s)
  have hc := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.diagramColimitMap_sourceComparison W U' U q'
    (fun s => hp' (K.obj s)) q (fun s => hp (K.obj s)) β f σ he
      (fun a => hA' (K.map a)) (fun a => hA (K.map a))
  exact hc

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
