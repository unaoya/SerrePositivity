module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFirstFactorWordActionFunctors
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedPrefixHammock
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.MarkedZigzagReflection

/-!
# 語の圧縮後の元の指定 prefix の W-hammock

概要：像の最小列の prefix を元の指定部分圏へ持ち上げ、元の語の作用と照合する。
方針：最小列の像の等式と包含後の全関手の比較を元の持ち上げで反映する。
規約：指定部分圏の実際の全関手と元の全行・全縦射を保持する。
使われ方：指定因子の W-hammock 余極限の標準射の像の一致。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ [])

lemma prefix_arrow_mem_of_first (i : Fin w.length) (hi : i = firstColumn W (τ.obj 0) h)
    (hi0 : column W (τ.obj 0) i ≠ []) (d : Fin (n.unop.len + 1))
    (k : Fin (Word.CutFactor.prefixWord w i).length) :
    W.paths (((prefixDiagram W τ i hi0).obj d).arrow k) := by
  cases hi
  exact AttachedPrefix.arrow_mem W τ h d k

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (h : ∃ i, column W (τ.obj 0) i ≠ [])
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0)
    (f.orderHom (AttachedPrefix.index W τ h)) ≠ [])

include hT in
lemma imagePrefix_arrow_mem (d : Fin (n.unop.len + 1))
    (k : Fin (prefixWord b (f.orderHom (AttachedPrefix.index W τ h))).length) :
    W.paths (((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d).arrow k) :=
  Attachments.prefix_arrow_mem_of_first W (τ ⋙ WordAction.functor f)
    ⟨f.orderHom (AttachedPrefix.index W τ h), hT⟩ _
    (firstColumn_wordAction W f (τ.obj 0) h ⟨_, hT⟩).symm hT d k

def markedImagePrefixFunctor := MarkedZigzag.liftFunctor W.paths
  (Attachments.prefixFunctor W (τ ⋙ WordAction.functor f)
    (f.orderHom (AttachedPrefix.index W τ h)) hT) (imagePrefix_arrow_mem W f τ h hT)

include hT in
lemma marked_prefix_functor_heq :
    HEq (AttachedPrefix.markedFunctor W τ h ⋙ WordAction.functor
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)))
    (markedImagePrefixFunctor W f τ h hT) := by
  let fp := prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)
  let I := Zigzag.Relative.functor (w := prefixWord b (f.orderHom (AttachedPrefix.index W τ h)))
    (X := (⟨X⟩ : WideSubcategory W.paths))
    (Y := (⟨(rowGenerator W τ (AttachedPrefix.index W τ h)
      (AttachedPrefix.nonempty W τ h)).left⟩ : WideSubcategory W.paths))
    (MarkedZigzag.inclusion W.paths)
  have he : (AttachedPrefix.markedFunctor W τ h ⋙ WordAction.functor fp) ⋙ I =
      AttachedPrefix.functor W τ h ⋙ WordAction.functor fp := by
    rw [Functor.assoc, ← Zigzag.Relative.wordAction_functor_eq, ← Functor.assoc]
    rw [AttachedPrefix.markedFunctor_inclusion]
  have hr := MarkedZigzag.liftFunctor_inclusion W.paths
    (Attachments.prefixFunctor W (τ ⋙ WordAction.functor f)
      (f.orderHom (AttachedPrefix.index W τ h)) hT) (imagePrefix_arrow_mem W f τ h hT)
  exact MarkedZigzag.functor_heq_of_inclusion W.paths rfl rfl
    (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (generator_eq W f τ h hT)).symm _ _
    ((heq_of_eq he).trans ((prefix_functor_heq W f τ h hT).trans (heq_of_eq hr).symm))

include hT in
lemma marked_prefix_functor :
    AttachedPrefix.markedFunctor W τ h ⋙ WordAction.functor
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h)) ⋙
      Zigzag.EndpointChange.functor rfl
        (congrArg (fun Z : Paths C => (⟨Z⟩ : WideSubcategory W.paths))
          (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
            (generator_eq W f τ h hT)).symm) = markedImagePrefixFunctor W f τ h hT :=
  Zigzag.EndpointChange.comp_eq_of_heq rfl _ _ _ (marked_prefix_functor_heq W f τ h hT)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
