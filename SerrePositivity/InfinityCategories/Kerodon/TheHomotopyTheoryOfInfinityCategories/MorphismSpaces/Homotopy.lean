module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionRetraction

/-!
概要：宇宙の持ち上げによる単体的ホモトピーと同値の保存。
方針：円筒の各単体で ULift を外して元のホモトピーを評価する。
規約：単位区間の標準単体も新しい宇宙に移す。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、coherent nerve の Hom 比較の宇宙調整。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：単体的ホモトピーの宇宙を持ち上げる。
方針：各次数で入力の ULift を外し、出力を ULift する。
規約：単位区間の単体は同じ順序写像の ULift として戻す。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、写像空間の比較のホモトピー逆。 -/
def uliftSimplicialHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g) where
  h :=
    { app d := ↾fun x ↦ ULift.up (H.h.app d (x.1.down, ULift.up x.2.down))
      naturality d e α := by
        apply ConcreteCategory.hom_ext
        intro x
        apply ULift.ext
        have hn := H.h.naturality α
        exact congrArg (fun (k : (X ⊗ Δ[1]).obj d ⟶ Y.obj e) ↦
          k (x.1.down, ULift.up x.2.down)) hn }
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact ConcreteCategory.congr_hom (C := Type u)
      (congrArg (fun (a : X ⟶ Y) ↦ a.app d) H.h₀) x.down
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact ConcreteCategory.congr_hom (C := Type u)
      (congrArg (fun (a : X ⟶ Y) ↦ a.app d) H.h₁) x.down
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：単体的ホモトピー同値は宇宙の持ち上げで保たれる。
方針：逆射を関手で写し、二つのホモトピーの宇宙を持ち上げる。
規約：Kan 性はこの主張には不要。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較射の二宇宙版への移行。 -/
lemma IsSimplicialHomotopyEquivalence.ulift {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  refine ⟨(SSet.uliftFunctor.{v, u}).map g, ?_, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, ← (SSet.uliftFunctor.{v, u}).map_id X]
    exact ⟨uliftSimplicialHomotopy H⟩
  · rw [← CategoryTheory.Functor.map_comp, ← (SSet.uliftFunctor.{v, u}).map_id Y]
    exact ⟨uliftSimplicialHomotopy K⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsSimplicialHomotopyEquivalence (ulift)


/-- 概要：Kan 複体間の同値は宇宙の持ち上げで保たれる。
方針：単体的ホモトピー逆を持ち上げ、Kan 複体間の同値へ戻す。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、豊穣 Hom の比較の同値性。 -/
lemma IsQCatEquivalence.ulift_of_kan {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f : X ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map f) :=
  hf.isSimplicialHomotopyEquivalence.ulift.isQCatEquivalence

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsQCatEquivalence (ulift_of_kan)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
