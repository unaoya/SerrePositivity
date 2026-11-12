module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransCompositionDiagram
/-!
概要：同じ順序相構成の定値図式と一変換図式を、元の dg 関手と指定ホモトピーへ同定する。
方針：全係数の異種等号と単位則、三つの有効な相の組を使う。
規約：全単体で比較する。使われ方：実関手圏写像の元の頂点・辺の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 元の定値関手図式の全単体は、元の dg 関手で写した単体そのもの。 -/
lemma dgOrderedFunctorSimplex_const {I : Type t} [Preorder I]
    (F : DGFunctor R C E) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) (β : Fin (n + 1) →o I) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor ((Functor.const I).obj (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E))).simplex
        s β = s.map F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl ?_
  apply heq_of_eq
  funext J a b k hJ ha hb hk
  exact _root_.SerrePositivity.DifferentialGraded.unit_compose R _
/-- 一変換の順序相図式の各対象は、元の二相の指定対象と一致する。 -/
lemma dgOrderedFunctorArrow_obj {F G : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    (p : Fin 2) (x : C) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor
      (ComposableArrows.mk₁ (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))).obj p).obj x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj F G p x := by fin_cases p <;> rfl
/-- 一変換の順序相輸送は、元の同じ厳密変換の輸送と異種等号で一致する。 -/
lemma dgOrderedFunctorArrow_transition {F G : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    {x y : C} {k : ℤ} (p q : Fin 2) (hpq : p ≤ q) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y k) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor
      (ComposableArrows.mk₁ (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))).transition p q hpq
        f)
      (η.transition p q hpq f) := by
  fin_cases p <;> fin_cases q <;> simp at hpq
  · exact heq_of_eq (_root_.SerrePositivity.DifferentialGraded.unit_compose R _)
  · rfl
  · exact heq_of_eq (_root_.SerrePositivity.DifferentialGraded.unit_compose R _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
private lemma heqDependentFunext {α : Sort u} {β γ : α → Sort v}
    {f : ∀ a, β a} {g : ∀ a, γ a} (h : ∀ a, HEq (f a) (g a)) : HEq f g :=
  Function.hfunext rfl (fun a b hab => by
    have he : a = b := eq_of_heq hab
    subst b
    exact h a)
/-- 一変換の順序相図式の全単体は、元の指定厳密変換のホモトピー単体と一致する。 -/
lemma dgOrderedFunctorArrow_simplex {F G : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOrderedFunctorDiagramOfFunctor
      (ComposableArrows.mk₁ (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η))).simplex s β =
      η.simplex s β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext (funext (fun a => dgOrderedFunctorArrow_obj η (β a) (s.obj a))) ?_
  apply heqDependentFunext
  intro I
  apply heqDependentFunext
  intro a
  apply heqDependentFunext
  intro b
  apply heqDependentFunext
  intro k
  apply heqDependentFunext
  intro hI
  apply heqDependentFunext
  intro ha
  apply heqDependentFunext
  intro hb
  apply heqDependentFunext
  intro hk
  exact dgOrderedFunctorArrow_transition η (β a) (β b) _ (s.hom I a b k hI ha hb hk)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
