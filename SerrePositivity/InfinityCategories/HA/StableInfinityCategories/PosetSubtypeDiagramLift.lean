module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeNerve

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def posetSubtypeDiagramLift {P : Type u} [PartialOrder P] (T : P → Prop)
    {A : SSet.{u}} (f : A ⟶ nerve P) (hf : ∀ v : A _⦋0⦌, T (nerveEquiv (f.app _ v))) :
    A ⟶ nerve {p : P // T p} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun v ↦ T (nerveEquiv v)) f hf ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso T).inv

lemma posetSubtypeDiagramLift_projection {P : Type u} [PartialOrder P] (T : P → Prop)
    {A : SSet.{u}} (f : A ⟶ nerve P) (hf : ∀ v : A _⦋0⦌, T (nerveEquiv (f.app _ v))) :
    posetSubtypeDiagramLift T f hf ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion T) = f := by
  rw [posetSubtypeDiagramLift, ← _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeNerveIso_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
