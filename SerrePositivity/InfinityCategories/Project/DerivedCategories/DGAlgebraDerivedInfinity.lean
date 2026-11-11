module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeProjectiveEquivalence
public import Mathlib.CategoryTheory.Monoidal.Mon
/-!
概要：非可換 dg 代数の右半自由加群による導来 ∞ 圏。
方針：既存の複体のモノイド対象を一対象 dg 圏にし、全 Hom end の半自由模型を使う。
規約：積の可換性を要求しない。反変加群が右作用になる向きに一対象圏を反転する。
使われ方：β5 の D(A) と相対テンソルの始域・終域。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped MonObj
variable (R : Type u) [CommRing R]
/-- 非可換 dg 代数の一対象圏の唯一の対象。 -/
inductive DGAlgebraPoint (B : Mon (Complex R)) : Type
  | star
/-- 一対象 dg 圏の対象は一意。 -/
instance (B : Mon (Complex R)) : Unique (DGAlgebraPoint R B) where
  default := .star
  uniq x := by cases x; rfl
/-- 積を順方向の合成とする dg 圏。右加群に使う圏はこの反対圏。 -/
instance dgAlgebraPointEnrichment (B : Mon (Complex R)) : DGCategory R (DGAlgebraPoint R B) where
  Hom _ _ := B.X
  id _ := η[B.X]
  comp _ _ _ := μ[B.X]
  id_comp _ _ := by rw [MonObj.one_mul, Iso.inv_hom_id]
  comp_id _ _ := by rw [MonObj.mul_one, Iso.inv_hom_id]
  assoc _ _ _ _ := by rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
/-- 非可換積が通常順の合成となる一対象 dg 圏。 -/
abbrev dgAlgebraCategory (B : Mon (Complex R)) := (DGAlgebraPoint R B)ᵒᵖ
/-- 非可換 dg 代数上の、実半自由 filtration を持つ右 dg 加群。 -/
abbrev SemifreeDGAlgebraModules (B : Mon (Complex R)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R (dgAlgebraCategory R B)
/-- D(B) := N_dg(Semifree(B))。B は可換性を要求しない複体のモノイド対象。 -/
abbrev dgAlgebraDerivedInfinityCategory (B : Mon (Complex R)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R (dgAlgebraCategory R B)
/-- 任意の非可換 dg 代数の半自由模型による導来 ∞ 圏は安定。 -/
theorem dgAlgebraDerivedInfinityCategory_isStable (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgAlgebraDerivedInfinityCategory R B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R (dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
