module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：標準 pinched Hom と宇宙持ち上げを厳密に交換する。
方針：元の単体と端点条件を ULift で往復し、面と退化を元の単体で照合する。
規約：quasicategory 性は不要。順方向の自然性も元の pinchedHomMap に対して保持する。
使われ方：小さい底の実際の Yoneda 写像の Hom 作用を、持ち上げた元の写像空間へ戻す。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 右 pinched 単体の宇宙を持ち上げる。 -/
def uliftPinchedSimplex {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (X := (SSet.uliftFunctor.{v, u}).obj C) (ULift.up x) (ULift.up y) n where
  val := ULift.up s.val
  source := congrArg ULift.up s.source
  target := congrArg ULift.up s.target

/-- 持ち上げた右 pinched 単体を元の宇宙へ戻す。 -/
def downPinchedSimplex {C : SSet.{u}} {x y : C _⦋0⦌} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (X := (SSet.uliftFunctor.{v, u}).obj C)
      (ULift.up x) (ULift.up y) n) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex x y n where
  val := s.val.down
  source := congrArg ULift.down s.source
  target := congrArg ULift.down s.target

/-- 宇宙の持ち上げと右 pinched Hom は、面と退化を保って厳密に同型。 -/
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

/-- 宇宙持ち上げの Hom 同型は、元の写像の全 pinched Hom 作用と厳密に可換。 -/
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

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
