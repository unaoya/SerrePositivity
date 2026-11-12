module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Homotopy

/-!
概要：宇宙を持ち上げた Kan 複体間の同値から元の同値を回収する。
方針：逆射と単体的ホモトピーの各値の ULift を外す。
規約：単体的ホモトピー同値の反映には Kan 性は不要で、圏同値の判定で Kan 性を用いる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の transport の判定を元の係数の射へ戻す。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：持ち上げた二つの単体集合の間の射を元の宇宙へ戻す。
方針：入力を ULift して評価し、出力の ULift を外す。
規約：もとの射が ULift で与えられているとは仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げた同値の逆射を元の宇宙へ戻す。 -/
def uliftMorphismDown {X Y : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y) : X ⟶ Y where
  app d := ↾fun x ↦ (f.app d (ULift.up x)).down
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k : ((SSet.uliftFunctor.{v, u}).obj X).obj d ⟶
      ((SSet.uliftFunctor.{v, u}).obj Y).obj e ↦ (k (ULift.up x)).down) (f.naturality α)

/-- 概要：射を宇宙持ち上げしてから戻すと元の射になる。
方針：各次数の値の ULift の往復を計算する。
規約：射の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、逆射の二つの合成の同定。 -/
lemma uliftMorphismDown_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    uliftMorphismDown ((SSet.uliftFunctor.{v, u}).map f) = f := rfl

/-- 概要：持ち上げた射の合成を元の宇宙へ戻す操作は合成を保つ。
方針：中間の ULift.up と ULift.down を消去する。
規約：二つの射は元の宇宙から来た射でなくてもよい。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げたホモトピー逆の二つの合成を戻す。 -/
lemma uliftMorphismDown_comp {X Y Z : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y)
    (g : (SSet.uliftFunctor.{v, u}).obj Y ⟶ (SSet.uliftFunctor.{v, u}).obj Z) :
    uliftMorphismDown (f ≫ g) = uliftMorphismDown f ≫ uliftMorphismDown g := rfl

/-- 概要：持ち上げた単体集合の恒等射を元の宇宙へ戻すと恒等射になる。
方針：各次数の入力の ULift の往復を計算する。
規約：単体集合は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、ホモトピー逆の恒等条件を戻す。 -/
lemma uliftMorphismDown_id (X : SSet.{u}) :
    uliftMorphismDown (𝟙 ((SSet.uliftFunctor.{v, u}).obj X)) = 𝟙 X := rfl

/-- 概要：持ち上げた単体集合間の単体的ホモトピーを元の宇宙へ戻す。
方針：円筒の標準単体の順序写像を同じものとして評価し、全空間の値の ULift を外す。
規約：元の射の宇宙への帰着と同じ操作を二端点に適用する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げた同値の単位・余単位を元へ戻す。 -/
def unliftSimplicialHomotopy {X Y : SSet.{u}}
    {f g : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y}
    (H : SSet.Homotopy f g) : SSet.Homotopy (uliftMorphismDown f) (uliftMorphismDown g) where
  h :=
    { app d := ↾fun x ↦ (H.h.app d (ULift.up x.1, ULift.up x.2.down)).down
      naturality d e α := by
        apply ConcreteCategory.hom_ext
        intro x
        exact congrArg (fun k : (((SSet.uliftFunctor.{v, u}).obj X) ⊗ Δ[1]).obj d ⟶
          ((SSet.uliftFunctor.{v, u}).obj Y).obj e ↦
          (k (ULift.up x.1, ULift.up x.2.down)).down) (H.h.naturality α) }
  h₀ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.down
      (ConcreteCategory.congr_hom (C := Type (max u v))
        (congrArg (fun k : (SSet.uliftFunctor.{v, u}).obj X ⟶
          (SSet.uliftFunctor.{v, u}).obj Y ↦ k.app d) H.h₀) (ULift.up.{v, u} x))
  h₁ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.down
      (ConcreteCategory.congr_hom (C := Type (max u v))
        (congrArg (fun k : (SSet.uliftFunctor.{v, u}).obj X ⟶
          (SSet.uliftFunctor.{v, u}).obj Y ↦ k.app d) H.h₁) (ULift.up.{v, u} x))
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：宇宙持ち上げは単体的ホモトピー同値を反映する。
方針：持ち上げた逆射と二つのホモトピーを元の宇宙へ戻す。
規約：元の二つの単体集合の Kan 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、係数の同値の宇宙への依存を除く。 -/
lemma IsSimplicialHomotopyEquivalence.of_ulift {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence ((SSet.uliftFunctor.{v, u}).map f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := h
  refine ⟨uliftMorphismDown g, ?_, ?_⟩
  · have h := unliftSimplicialHomotopy H
    simpa only [uliftMorphismDown_comp, uliftMorphismDown_map, uliftMorphismDown_id]
      using (Nonempty.intro h)
  · have h := unliftSimplicialHomotopy K
    simpa only [uliftMorphismDown_comp, uliftMorphismDown_map, uliftMorphismDown_id]
      using (Nonempty.intro h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsSimplicialHomotopyEquivalence (of_ulift)


/-- 概要：Kan 複体間の射の圏同値性は宇宙持ち上げで保存・反映される。
方針：保存と、単体的ホモトピー逆を元の宇宙へ戻す反映を組み合わせる。
規約：両端の Kan 性を要求する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent な復元の判定を元の Kan 複体の射で述べる。 -/
lemma isQCatEquivalence_ulift_iff_of_kan {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((SSet.uliftFunctor.{v, u}).map f) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f :=
  ⟨fun h ↦ h.isSimplicialHomotopyEquivalence.of_ulift.isQCatEquivalence,
    fun h ↦ h.ulift_of_kan⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
