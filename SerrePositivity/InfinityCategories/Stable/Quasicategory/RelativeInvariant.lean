module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.Pointed
public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams

/-!
分割で生成：docstring を書き直すこと
概要：提示源 S 上の局所化不変量と、ν の像が Verdier となる実四角形。
方針：全ての図式を S 内で指定し、ν と値関手を別々に後合成する。
規約：値関手の StableInfinity への延長を仮定しない。使われ方：厳密 dg 入力の K。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の S 内の四角形と、その ν 像の Verdier 提示。 -/
structure RelativeVerdierDiagram {S : SSet.{u + 1}} (ν : S ⟶ StableInfinity.{u}) where
  square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S
  image : VerdierDiagram.{u}
  image_eq : square ≫ ν = image.square

namespace RelativeVerdierDiagram
variable {S : SSet.{u + 1}} {ν : S ⟶ StableInfinity.{u}} (d : RelativeVerdierDiagram ν)

lemma zero_corner :
    IsZeroCategory (stableObject (ν.app (Opposite.op ⦋0⦌) (squareVertex d.square 0 1))) := by
  have h := d.image.zero_corner
  rw [← d.image_eq] at h
  exact h

/-- 絶対 Verdier 図式を恒等提示源の相対図式と見る。 -/
def ofAbsolute (d : VerdierDiagram.{u}) : RelativeVerdierDiagram (𝟙 StableInfinity.{u}) :=
  ⟨d.square, d, Category.comp_id _⟩

end RelativeVerdierDiagram

end SerrePositivity.KST.LocalizingInvariants
