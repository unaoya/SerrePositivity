module

public import SerrePositivity.EInfinity.Hammock.AllMarkedSimplex
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

abbrev nativeGraph (w : Word) := graph (⊤ : MorphismProperty (WideSubcategory W.paths))
  w (⟨X⟩ : WideSubcategory W.paths) ⟨Y⟩

def nativeSpace : SSet.{max u v} :=
  colimitGraph (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩

def nativeInclusion (w : Word) : nativeGraph W X Y w ⟶ nativeSpace W X Y :=
  graphInclusion (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ w

def graphMap (w : Word) : nativeGraph W X Y w ⟶ graph W.paths w X Y :=
  nerveMap (Zigzag.Relative.functor (MarkedZigzag.inclusion W.paths))

def inclusion : nativeSpace W X Y ⟶ colimitGraph W.paths X Y :=
  Relative.colimitMap (MarkedZigzag.inclusion W.paths) ⟨X⟩ ⟨Y⟩

lemma nativeInclusion_inclusion (w : Word) :
    nativeInclusion W X Y w ≫ inclusion W X Y = graphMap W X Y w ≫ graphInclusion W.paths X Y w :=
  Relative.graphInclusion_colimitMap (MarkedZigzag.inclusion W.paths) ⟨X⟩ ⟨Y⟩ w

variable {X Y} {w : Word} {n m : SimplexCategoryᵒᵖ}

def lift (τ : (graph W.paths w X Y).obj n) (h : Holds W τ) :
    (nativeGraph W X Y w).obj n := MarkedZigzag.liftFunctor W.paths τ h

lemma lift_inclusion (τ : (graph W.paths w X Y).obj n) (h : Holds W τ) :
    (graphMap W X Y w).app n (lift W τ h) = τ := rfl

lemma graphMap_holds (τ : (nativeGraph W X Y w).obj n) :
    Holds W ((graphMap W X Y w).app n τ) := fun d j => ((τ.obj d).arrow j).property

lemma lift_reflection (τ : (nativeGraph W X Y w).obj n) :
    lift W ((graphMap W X Y w).app n τ) (graphMap_holds W τ) = τ := rfl

lemma lift_simplex (τ : (graph W.paths w X Y).obj n) (h : Holds W τ) (θ : n ⟶ m)
    (hθ : Holds W ((graph W.paths w X Y).map θ τ)) :
    lift W ((graph W.paths w X Y).map θ τ) hθ = (nativeGraph W X Y w).map θ (lift W τ h) := rfl

lemma lift_word {a b : Word} (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (h : Holds W τ)
    (hf : Holds W (τ ⋙ WordAction.functor f)) :
    lift W (τ ⋙ WordAction.functor f) hf = lift W τ h ⋙ WordAction.functor f := by
  apply eq_of_heq
  apply MarkedZigzag.functor_heq_of_inclusion W.paths rfl rfl rfl
  apply heq_of_eq
  change MarkedZigzag.liftFunctor W.paths _ _ ⋙ _ = (_ ⋙ _) ⋙ _
  rw [MarkedZigzag.liftFunctor_inclusion, Functor.assoc,
    ← Zigzag.Relative.wordAction_functor_eq, ← Functor.assoc]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
