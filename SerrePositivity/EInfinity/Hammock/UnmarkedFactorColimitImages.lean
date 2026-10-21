module

public import SerrePositivity.EInfinity.Hammock.UnmarkedMarkedImagePrefix
public import SerrePositivity.EInfinity.Hammock.EndpointColimit

/-!
# 元の切断因子の同じ hammock 余極限の像

概要：語の作用の前後の prefix・残りの標準射の像を元の端点表示の移送で照合する。
方針：元の全関手の厳密な比較と同じ標準余錐の自然性を使う。
規約：指定 prefix は実際の指定部分圏の W-hammock でも比較する。
使われ方：因子の全語の余極限への降下と自由積分解。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (h : ∃ i, column W (τ.obj 0) i ≠ [])
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0)
    (f.orderHom (AttachedPrefix.index W τ h)) ≠ [])

include hT in
lemma prefix_colimit_image :
    let i := AttachedPrefix.index W τ h
    let A : Paths C := (rowGenerator W τ i (AttachedPrefix.nonempty W τ h)).left
    let A' : Paths C := (rowGenerator W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).left
    let hp : A = A' := (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (generator_eq W f τ h hT)).symm
    (EndpointChange.colimitMap W.paths rfl hp).app n
      ((graphInclusion W.paths X A (prefixWord a i)).app n (AttachedPrefix.functor W τ h)) =
    (graphInclusion W.paths X A' (prefixWord b (f.orderHom i))).app n
      (Attachments.prefixFunctor W (τ ⋙ WordAction.functor f) (f.orderHom i) hT) :=
  EndpointChange.image_eq W.paths
    (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)) rfl _
    (AttachedPrefix.functor W τ h)
    (Attachments.prefixFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) (prefix_functor W f τ h hT)

include hT in
lemma residual_colimit_image :
    let i := AttachedPrefix.index W τ h
    let B : Paths C := (rowGenerator W τ i (AttachedPrefix.nonempty W τ h)).right
    let B' : Paths C := (rowGenerator W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).right
    let hp : B = B' := (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
      (generator_eq W f τ h hT)).symm
    (EndpointChange.colimitMap W.paths hp rfl).app n
      ((graphInclusion W.paths B Y (residualWord a i)).app n
        (Attachments.residualFunctor W τ i (AttachedPrefix.nonempty W τ h))) =
    (graphInclusion W.paths B' Y (residualWord b (f.orderHom i))).app n
      (Attachments.residualFunctor W (τ ⋙ WordAction.functor f) (f.orderHom i) hT) :=
  EndpointChange.image_eq W.paths
    (residualMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)) _ rfl
    (Attachments.residualFunctor W τ (AttachedPrefix.index W τ h) (AttachedPrefix.nonempty W τ h))
    (Attachments.residualFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) (residual_functor W f τ h hT)

include hT in
lemma marked_prefix_colimit_image :
    let i := AttachedPrefix.index W τ h
    let A : Paths C := (rowGenerator W τ i (AttachedPrefix.nonempty W τ h)).left
    let A' : Paths C := (rowGenerator W (τ ⋙ WordAction.functor f) (f.orderHom i) hT).left
    let hp : A = A' := (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (generator_eq W f τ h hT)).symm
    (EndpointChange.colimitMap (⊤ : MorphismProperty (WideSubcategory W.paths)) rfl
      (congrArg (fun Z : Paths C => (⟨Z⟩ : WideSubcategory W.paths)) hp)).app n
      ((graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths))
        ⟨X⟩ ⟨A⟩ (prefixWord a i)).app n (AttachedPrefix.markedSimplex W τ h)) =
    (graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths))
      ⟨X⟩ ⟨A'⟩ (prefixWord b (f.orderHom i))).app n (markedImagePrefixFunctor W f τ h hT) :=
  EndpointChange.image_eq (⊤ : MorphismProperty (WideSubcategory W.paths))
    (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)) rfl _
    (AttachedPrefix.markedSimplex W τ h) (markedImagePrefixFunctor W f τ h hT)
    (marked_prefix_functor W f τ h hT)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
