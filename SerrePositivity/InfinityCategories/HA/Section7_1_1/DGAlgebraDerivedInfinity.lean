module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeProjectiveEquivalence
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
namespace SerrePositivity.InfinityCategories.HA.Section7_1_1
open _root_.CategoryTheory MonoidalCategory _root_.SerrePositivity.DifferentialGraded _root_.SSet
open scoped _root_.CategoryTheory.MonObj
variable (R : Type u) [CommRing R]
/-- 非可換 dg 代数の一対象圏の唯一の対象。 -/
inductive DGAlgebraPoint (B : Mon (Complex R)) : Type
  | star
/-- 一対象 dg 圏の対象は一意。 -/
instance (B : Mon (Complex R)) : Unique (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) where
  default := .star
  uniq x := by cases x; rfl
/-- 積を順方向の合成とする dg 圏。右加群に使う圏はこの反対圏。 -/
instance dgAlgebraPointEnrichment (B : Mon (Complex R)) : DGCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B) where
  Hom _ _ := B.X
  id _ := η[B.X]
  comp _ _ _ := μ[B.X]
  id_comp _ _ := by rw [MonObj.one_mul, Iso.inv_hom_id]
  comp_id _ _ := by rw [MonObj.mul_one, Iso.inv_hom_id]
  assoc _ _ _ _ := by rw [MonObj.mul_assoc, Iso.inv_hom_id_assoc]
/-- 非可換積が通常順の合成となる一対象 dg 圏。 -/
abbrev dgAlgebraCategory (B : Mon (Complex R)) := (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint R B)ᵒᵖ
/-- 非可換 dg 代数上の、実半自由 filtration を持つ右 dg 加群。 -/
abbrev SemifreeDGAlgebraModules (B : Mon (Complex R)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
/-- D(B) := N_dg(Semifree(B))。B は可換性を要求しない複体のモノイド対象。 -/
abbrev dgAlgebraDerivedInfinityCategory (B : Mon (Complex R)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
/-- 任意の非可換 dg 代数の半自由模型による導来 ∞ 圏は安定。 -/
theorem dgAlgebraDerivedInfinityCategory_isStable (B : Mon (Complex R)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraDerivedInfinityCategory R B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R B)
end SerrePositivity.InfinityCategories.HA.Section7_1_1

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.1.4" (partial := component) "仮定：可換環 R 上の任意の厳密な非可換 dg 代数（Lean が強い：複体上の dg 加群の自己作用の模型の場合）。結論：右半自由加群の dg nerve による導来 ∞ 圏が安定となる（加群圏の安定性の部分に一致）。一般の左テンソル作用と忘却による完全性の反映は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraDerivedInfinityCategory_isStable
attribute [cite HA "7.1.1.5" (partial := special) "仮定：可換環 R 上の非可換 dg 代数（Lean が強い：この dg 模型の場合）。結論：右 dg 加群の導来 ∞ 圏が安定となる（右加群の安定性の部分に一致）。任意の環スペクトルの左右加群の模型との比較は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraDerivedInfinityCategory_isStable
attribute [cite HA "7.1.4.2" (partial := direction) "仮定：可換環 R と複体のモノイド対象 B（HA と一致）。結論：同じ複体・単位・乗法を Hom・恒等・合成とする一対象 dg 代数を構成する（HA の同定のこの向きに一致）。逆向きの関手と両合成の自然同型は含まれない。"] _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraPointEnrichment
