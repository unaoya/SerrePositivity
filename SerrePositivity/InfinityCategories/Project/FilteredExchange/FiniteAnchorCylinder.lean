module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.GluedFiberDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalEndpointPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutDisjoint

/-!
概要：有限な境界の非単射な因子分解を、通常の有限写像円柱の単射に置き換える。
方針：区間の始点を元の射で貼り、交わらない終点を境界として残す。
規約：単射性は元の境界射には要求しない。
使われ方：指定境界を保つ相対持ち上げへの有限データの入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：境界射の通常の写像円柱。
方針：始点を元の射で貼る。規約：有限なら有限。使われ方：単射な境界の用意。 -/
def anchorCylinder {A L : SSet.{u}} (a : A ⟶ L) : SSet.{u} :=
  pushout (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a

/-- 概要：残した終点による境界の包含。
方針：終点を円柱側から入れる。規約：元の射は任意。使われ方：単射な境界。 -/
def anchorCylinderIn {A L : SSet.{u}} (a : A ⟶ L) : A ⟶ anchorCylinder a :=
  SSet.ι₁ ≫ pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a

/-- 概要：新しい境界の包含は単射。
方針：貼った始点と残した終点の不交性を用いる。
規約：元の a の単射性は不要。使われ方：相対円柱持ち上げの前提。 -/
instance anchorCylinderIn_mono {A L : SSet.{u}} (a : A ⟶ L) : Mono (anchorCylinderIn a) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mono_pushout_inl_comp_of_disjoint (IsPushout.of_hasPushout _ _)
  intro n x y h
  have hh := congrArg (fun s : (A ⊗ (Δ[1] : SSet.{u})).obj n ↦
    (stdSimplex.objEquiv s.2).toOrderHom 0) h
  exact (by decide : (0 : Fin 2) ≠ 1) hh

/-- 概要：有限な境界と有限な因子分解の写像円柱は有限。
方針：区間との積と有限押し出しの有限性を使う。
規約：元の a は任意。使われ方：filtered な底の有限図式の収縮。 -/
instance anchorCylinder_finite {A L : SSet.{u}} [A.Finite] [L.Finite] (a : A ⟶ L) :
    (anchorCylinder a).Finite := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_pushout _ a

/-- 概要：有限写像円柱から元の因子分解先への射影。
方針：円柱では時間を忘れ、元の因子分解先では恒等。
規約：元の境界射に厳密に重なる。使われ方：元の全空間への指定射の保持。 -/
def anchorCylinderOut {A L : SSet.{u}} (a : A ⟶ L) : anchorCylinder a ⟶ L :=
  pushout.desc (fst A (Δ[1] : SSet.{u}) ≫ a) (𝟙 L) (by
    change (𝟙 A) ≫ a = a ≫ 𝟙 L
    rw [Category.id_comp, Category.comp_id])

/-- 概要：新しい境界と射影の合成は元の指定境界射。
方針：円柱側の制限と終点の射影を計算する。
規約：厳密な等式。使われ方：境界を置き換えた因子分解の確認。 -/
lemma anchorCylinderIn_out {A L : SSet.{u}} (a : A ⟶ L) :
    anchorCylinderIn a ≫ anchorCylinderOut a = a := by
  rw [anchorCylinderIn, anchorCylinderOut, Category.assoc, pushout.inl_desc, ← Category.assoc]
  exact Category.id_comp _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
