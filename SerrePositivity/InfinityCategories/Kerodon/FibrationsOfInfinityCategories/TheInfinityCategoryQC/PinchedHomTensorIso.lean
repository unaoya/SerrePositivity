module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：直積の右写像空間と各因子の右写像空間の直積の同型。
方針：pinched 単体の値と端点条件を二つの成分に分ける。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：直積の右写像空間は各因子の右写像空間の直積と自然同型。
方針：pinched 単体を成分ごとに写して元の単体へ戻す。
規約：元の頂点・単体の値と後合成を保持する。
使われ方：lax pullback の二入力と両端の写像空間の表示。 -/
def pinchedHomTensorMap {X Y : SSet.{u}} (x y : (X ⊗ Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.1 y.1 ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.2 y.2 :=
  CartesianMonoidalCategory.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (fst X Y) x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (snd X Y) x y)
/-- 概要：直積の右写像空間は各因子の右写像空間の直積と自然同型。
方針：pinched 単体を成分ごとに写して元の単体へ戻す。
規約：元の頂点・単体の値と後合成を保持する。
使われ方：lax pullback の二入力と両端の写像空間の表示。 -/
def pinchedHomTensorInv {X Y : SSet.{u}} (x y : (X ⊗ Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.1 y.1 ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.2 y.2 ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y where
  app n := by
    rcases n with ⟨⟨n⟩⟩
    exact ↾fun z ↦ ⟨(z.1.val, z.2.val), Prod.ext z.1.source z.2.source,
      Prod.ext z.1.target z.2.target⟩
  naturality n m α := by
    rcases n with ⟨⟨n⟩⟩
    rcases m with ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro z
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    rfl
/-- 概要：直積の右写像空間は各因子の右写像空間の直積と自然同型。
方針：pinched 単体を成分ごとに写して元の単体へ戻す。
規約：元の頂点・単体の値と後合成を保持する。
使われ方：lax pullback の二入力と両端の写像空間の表示。 -/
def pinchedHomTensorIso {X Y : SSet.{u}} (x y : (X ⊗ Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.1 y.1 ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x.2 y.2 where
  hom := pinchedHomTensorMap x y
  inv := pinchedHomTensorInv x y
  hom_inv_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro z
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext <;> apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext <;> rfl
/-- 概要：直積の右写像空間は各因子の右写像空間の直積と自然同型。
方針：pinched 単体を成分ごとに写して元の単体へ戻す。
規約：元の頂点・単体の値と後合成を保持する。
使われ方：lax pullback の二入力と両端の写像空間の表示。 -/
lemma pinchedHomTensorIso_naturality {X Y X' Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (x y : (X ⊗ Y) _⦋0⦌) :
    (pinchedHomTensorIso x y).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x.1 y.1 ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap g x.2 y.2) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (f ⊗ₘ g) x y ≫
      (pinchedHomTensorIso ((f ⊗ₘ g).app (Opposite.op ⦋0⦌) x)
        ((f ⊗ₘ g).app (Opposite.op ⦋0⦌) y)).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext <;> apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
