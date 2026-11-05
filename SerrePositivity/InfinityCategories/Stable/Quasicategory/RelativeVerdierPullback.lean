module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.PastingShapes
public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeInvariant

/-!
分割で生成：docstring を書き直すこと
概要：提示源内の Verdier 比較長方形から、同じ値関手の実 pullback を導く。
方針：右面・外周の転置 Verdier 提示を E で写し、実 pullback 貼合せで右面を消す。
規約：長方形と全合成三角形を S 内で保持する。使われ方：相対版 K-8 d8。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- D2・β3 の S 内の持ち上げが供給する、右面と外周の Verdier 比較。 -/
structure RelativeVerdierRectangle {S : SSet.{u + 1}} (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}) where
  diagram : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S
  right : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierDiagram ν
  outer : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierDiagram ν
  right_eq : pastingSquare _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.diagram 0 = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.right.square
  outer_eq : pastingSquare _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.diagram 1 = (β_ _ _).hom ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.outer.square

namespace RelativeVerdierRectangle
open _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u}}
  (d : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle ν)

/-- ν 像の二つの Verdier 提示から、S 内の実長方形の相対証明書を作る。 -/
def ofImage (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u})
    (hR : pastingSquare (F ≫ ν) 0 = (β_ _ _).hom ≫ r.square)
    (hO : pastingSquare (F ≫ ν) 1 = (β_ _ _).hom ≫ o.square) :
    _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle ν where
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.diagram := F
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.right := ⟨(β_ _ _).hom ≫ pastingSquare F 0, r, by
    rw [Category.assoc]
    change (β_ _ _).hom ≫ pastingSquare (F ≫ ν) 0 = r.square
    rw [hR, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]⟩
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.outer := ⟨(β_ _ _).hom ≫ pastingSquare F 1, o, by
    rw [Category.assoc]
    change (β_ _ _).hom ≫ pastingSquare (F ≫ ν) 1 = o.square
    rw [hO, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]⟩
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.right_eq := by
    change _ = (β_ _ _).hom ≫ (β_ _ _).hom ≫ _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.outer_eq := by
    change _ = (β_ _ _).hom ≫ (β_ _ _).hom ≫ _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 元の二脚と比較三角形を含む S 内の比較正方形。 -/
def comparisonSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S :=
  (β_ _ _).hom ≫ pastingSquare d.diagram 2

end RelativeVerdierRectangle
end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.comparisonSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.comparisonSquare := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.comparisonSquare

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.diagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.diagram := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.diagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofImage := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.outer (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.outer := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.outer

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.outer_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.outer_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.right := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.right_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.right_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofImage._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofImage._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofImage._proof_3 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofImage._proof_4 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofImage._proof_5 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofImage._proof_5
