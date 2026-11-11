module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FinitePosetLeftKanExtension

/-!
概要：順序部分型の図式を元の順序集合へ厳密に延長する。
方針：全部分複体の同型と、有限局所余極限・指定終対象への延長を接続する。
規約：元の図式と指定した終対象を保持する。使われ方：一般安定性判定の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
def posetSubtypeInclusion {P : Type u} [PartialOrder P] (T : P → Prop) :
    {p : P // T p} ⥤ P :=
  (⟨Subtype.val, fun _ _ h ↦ h⟩ : {p : P // T p} →o P).toFunctor

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
def posetFullSubcomplexNerveLift {P : Type u} [PartialOrder P] (T : P → Prop) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v)) : SSet.{u}) ⟶
      nerve {p : P // T p} where
  app n := ↾fun s ↦
    { obj := fun i ↦ ⟨s.val.obj i, s.property (SimplexCategory.const ⦋0⦌ n.unop i)⟩
      map := fun f ↦ homOfLE (s.val.monotone (leOfHom f)) }
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f
      apply Subsingleton.elim
    · intro i
      apply Subtype.ext
      rfl

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
def posetSubtypeNerveIso {P : Type u} [PartialOrder P] (T : P → Prop) :
    nerve {p : P // T p} ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v)) : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun v ↦ T (nerveEquiv v))
    (nerveMap (posetSubtypeInclusion T)) (fun v ↦ (nerveEquiv v).property)
  inv := posetFullSubcomplexNerveLift T
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f
      apply Subsingleton.elim
    · intro i
      apply Subtype.ext
      rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply CategoryTheory.Functor.ext
    · intro i j f
      apply Subsingleton.elim
    · intro i
      rfl

/-- 元の順序部分型の全図式を厳密に保持する比較。 -/
lemma posetSubtypeNerveIso_hom_ι {P : Type u} [PartialOrder P] (T : P → Prop) :
    (posetSubtypeNerveIso T).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve P) (fun v ↦ T (nerveEquiv v))).ι =
      nerveMap (posetSubtypeInclusion T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ (fun v ↦ (nerveEquiv v).property)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
