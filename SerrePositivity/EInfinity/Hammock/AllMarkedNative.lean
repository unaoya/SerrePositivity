module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.AllMarkedSimplex
public import SerrePositivity.EInfinity.Hammock.RelativeColimitMap

/-!
# 指定部分圏の元の hammock と全指定単体の持ち上げ

概要：指定部分圏の実際の余極限と包含を固定し、元の全指定単体を持ち上げる。
方針：元の MarkedZigzag の全関手と標準射を再利用する。
規約：全語と元の全行・全列・全縦射を保持する。
使われ方：空文字列部分との同型。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y : Paths C)

abbrev nativeGraph (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (⊤ : MorphismProperty (WideSubcategory W.paths))
  w (⟨X⟩ : WideSubcategory W.paths) ⟨Y⟩

def nativeSpace : SSet.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩

def nativeInclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : nativeGraph W X Y w ⟶ nativeSpace W X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ w

def graphMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : nativeGraph W X Y w ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths))

def inclusion : nativeSpace W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y :=
  Relative.colimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths) ⟨X⟩ ⟨Y⟩

lemma nativeInclusion_inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    nativeInclusion W X Y w ≫ inclusion W X Y = graphMap W X Y w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y w :=
  Relative.graphInclusion_colimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths) ⟨X⟩ ⟨Y⟩ w

variable {X Y} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n m : SimplexCategoryᵒᵖ}

def lift (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ) :
    (nativeGraph W X Y w).obj n := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W.paths τ h

lemma lift_inclusion (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ) :
    (graphMap W X Y w).app n (lift W τ h) = τ := rfl

lemma graphMap_holds (τ : (nativeGraph W X Y w).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W ((graphMap W X Y w).app n τ) := fun d j => ((τ.obj d).arrow j).property

lemma lift_reflection (τ : (nativeGraph W X Y w).obj n) :
    lift W ((graphMap W X Y w).app n τ) (graphMap_holds W τ) = τ := rfl

lemma lift_simplex (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ) (θ : n ⟶ m)
    (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ)) :
    lift W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) hθ = (nativeGraph W X Y w).map θ (lift W τ h) := rfl

lemma lift_word {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)) :
    lift W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) hf = lift W τ h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f := by
  apply eq_of_heq
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.functor_heq_of_inclusion W.paths rfl rfl rfl
  apply heq_of_eq
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W.paths _ _ ⋙ _ = (_ ⋙ _) ⋙ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor_inclusion, Functor.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeWordAction.wordAction_functor_eq, ← Functor.assoc]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
