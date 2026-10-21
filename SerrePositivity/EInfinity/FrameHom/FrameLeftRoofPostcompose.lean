module

public import SerrePositivity.EInfinity.FrameHom.FrameLeftRoof
public import SerrePositivity.EInfinity.Hammock.LeftRoofPostcompose
public import SerrePositivity.EInfinity.Hammock.PointActions
public import SerrePositivity.EInfinity.Hammock.ColimitArrowMap
public import SerrePositivity.EInfinity.FrameHom.FrameSpanTargetHomotopy

/-!
# 元の frame の二列比較の後合成の自然性

概要：元の終域射による全単体の後合成を同じ二列と連結語で照合する。
方針：元の同方向列の collapse と全縦射の回収を使う。
規約：元の frame・全単体作用素・同じ元の射を保持する。
使われ方：既存 Map^h と reduced hammock の終域自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Opposite Hammock SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z : C} (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, W (p.app n)) (hA : ∀ {i j} (a : i ⟶ j), W (A.map a)) (g : Y ⟶ Z)

lemma frameLeftRoofFunctor_postcompose :
    (frameLeftRoofFunctor W A p hp hA (Y := Y)).prod'
        ((Functor.const _).obj (ForwardZigzag.obj (W := W) g)) ⋙
      ZigzagAppend.functor ⋙ WordAction.functor LeftRoof.postCollapse =
    ((cosimplicialHom A).map g).mapElements.op ⋙ frameLeftRoofFunctor W A p hp hA := by
  have ho (s : (((cosimplicialHom A).obj Y).Elements)ᵒᵖ) :
      WordAction.obj LeftRoof.postCollapse
        (ZigzagAppend.obj ((frameLeftRoofFunctor W A p hp hA).obj s)
          (ForwardZigzag.obj (W := W) g)) =
      (frameLeftRoofFunctor W A p hp hA).obj
        (((cosimplicialHom A).map g).mapElements.op.obj s) :=
    LeftRoof.postCollapse_obj W (p.app s.unop.obj.unop) (hp _) s.unop.val g
  apply CategoryTheory.Functor.hext ho
  intro s t a
  apply Zigzag.hom_hext (ho s) (ho t)
  intro j
  change HEq (ZigzagAppend.app ((frameLeftRoofFunctor W A p hp hA).map a)
    (𝟙 (ForwardZigzag.obj (W := W) g)) (LeftRoof.postCollapse.cut j)) _
  rw [LeftRoof.postCollapse_cut]
  fin_cases j
  · exact ZigzagAppend.app_left_heq ((frameLeftRoofFunctor W A p hp hA).map a)
      (𝟙 (ForwardZigzag.obj (W := W) g)) (0 : Fin 3)
  · exact ZigzagAppend.app_left_heq ((frameLeftRoofFunctor W A p hp hA).map a)
      (𝟙 (ForwardZigzag.obj (W := W) g)) (1 : Fin 3)
  · exact ZigzagAppend.app_right_heq ((frameLeftRoofFunctor W A p hp hA).map a)
      (𝟙 (ForwardZigzag.obj (W := W) g)) (1 : Fin 2)

def frameLeftRoofColimitMap :
    nerve (ULiftHom.{max u v} (((cosimplicialHom A).obj Y).Elements)ᵒᵖ) ⟶ colimitGraph W X Y :=
  frameLeftRoofNerveMap W A p hp hA ≫ graphInclusion W X Y LeftRoof.word

lemma frameLeftRoofColimitMap_postcompose :
    nerveMap (frameSpanTargetIndexMap A g) ≫ frameLeftRoofColimitMap W A p hp hA (Y := Z) =
      frameLeftRoofColimitMap W A p hp hA (Y := Y) ≫
        postcomposePointMap X (arrowMap W g) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let τ := σ ⋙ ULiftHom.down.{0, v, max u v}
  let Γ := τ ⋙ frameLeftRoofFunctor W A p hp hA (Y := Y)
  let Γ' := τ ⋙ ((cosimplicialHom A).map g).mapElements.op ⋙
    frameLeftRoofFunctor W A p hp hA (Y := Z)
  let T := Γ.prod' (arrowSimplex W g n) ⋙ ZigzagAppend.functor
  have hΓ : Γ' = T ⋙ WordAction.functor LeftRoof.postCollapse :=
    (congrArg (fun F => τ ⋙ F) (frameLeftRoofFunctor_postcompose W A p hp hA g)).symm
  have hι := congrArg (fun k => k.app n T)
    (graphInclusion_naturality W X Z LeftRoof.postCollapse)
  change (graphInclusion W X Z LeftRoof.word).app n Γ' =
    composePoint W X Y Z ((graphInclusion W X Y LeftRoof.word).app n Γ) (arrowPoint W g n)
  calc
    (graphInclusion W X Z LeftRoof.word).app n Γ' =
        (graphInclusion W X Z LeftRoof.word).app n
          (T ⋙ WordAction.functor LeftRoof.postCollapse) := congrArg _ hΓ
    _ = (graphInclusion W X Z LeftRoof.postWord).app n T := hι
    _ = composePoint W X Y Z ((graphInclusion W X Y LeftRoof.word).app n Γ)
        (arrowPoint W g n) :=
      (composePoint_inclusions W X Y Z LeftRoof.word (Word.single .forward)
        Γ (arrowSimplex W g n)).symm

end SerrePositivity.EInfinity.FrameHom
