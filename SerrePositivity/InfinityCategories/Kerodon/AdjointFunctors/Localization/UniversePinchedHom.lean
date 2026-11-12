module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps

/-!
概要：元の pinched Hom と宇宙持ち上げとの厳密同型。
方針：単体・端点条件を ULift で往復し、元の全 Hom 作用を保つ。
規約：新規の葉の中だけで宇宙操作を閉じ、既存 F1 は変更しない。
使われ方：局所化の全前合成の充満忠実性を同じ元の写像空間へ反映する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def uliftPinchedSimplex {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (X := (SSet.uliftFunctor.{v, u}).obj C) (ULift.up x) (ULift.up y) n where
  val := ULift.up s.val
  source := congrArg ULift.up s.source
  target := congrArg ULift.up s.target

def downPinchedSimplex {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (X := (SSet.uliftFunctor.{v, u}).obj C)
      (ULift.up x) (ULift.up y) n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n where
  val := s.val.down
  source := congrArg ULift.down s.source
  target := congrArg ULift.down s.target

def uliftPinchedHomIso {C : SSet.{u}} (x y : C _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := (SSet.uliftFunctor.{v, u}).obj C) (ULift.up x) (ULift.up y) :=
  NatIso.ofComponents (fun _ ↦ (Equiv.toIso
    { toFun := fun s ↦ uliftPinchedSimplex s.down
      invFun := fun s ↦ ULift.up (downPinchedSimplex s)
      left_inv := fun s ↦ by
        apply ULift.ext
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
        rfl
      right_inv := fun s ↦ by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
        rfl })) (by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    rfl)

lemma uliftPinchedHomIso_naturality {C D : SSet.{u}} (f : C ⟶ D) (x y : C _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y) ≫
      (uliftPinchedHomIso (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)).hom =
    (uliftPinchedHomIso x y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((SSet.uliftFunctor.{v, u}).map f) (ULift.up x) (ULift.up y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
