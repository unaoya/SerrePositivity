module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence

/-!
概要：元の射・円柱・ホモトピー逆の宇宙降下。
方針：各次数で入力を持ち上げて評価し、値の ULift を外す。
規約：既存 F1 の定義に依存しない葉で同じ操作を新名の名前空間に置く。
使われ方：局所化の実関手同型と全前合成の充満忠実性の降下。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def uliftMorphismDown {X Y : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y) : X ⟶ Y where
  app d := ↾fun x ↦ (f.app d (ULift.up x)).down
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun k : ((SSet.uliftFunctor.{v, u}).obj X).obj d ⟶
      ((SSet.uliftFunctor.{v, u}).obj Y).obj e ↦ (k (ULift.up x)).down) (f.naturality α)

lemma uliftMorphismDown_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    uliftMorphismDown ((SSet.uliftFunctor.{v, u}).map f) = f := rfl

lemma uliftMorphismDown_comp {X Y Z : SSet.{u}}
    (f : (SSet.uliftFunctor.{v, u}).obj X ⟶ (SSet.uliftFunctor.{v, u}).obj Y)
    (g : (SSet.uliftFunctor.{v, u}).obj Y ⟶ (SSet.uliftFunctor.{v, u}).obj Z) :
    uliftMorphismDown (f ≫ g) = uliftMorphismDown f ≫ uliftMorphismDown g := rfl

lemma uliftMorphismDown_id (X : SSet.{u}) :
    uliftMorphismDown (𝟙 ((SSet.uliftFunctor.{v, u}).obj X)) = 𝟙 X := rfl

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

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
