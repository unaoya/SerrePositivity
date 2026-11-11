module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparison
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
概要：全余錐族から元の図式と定値頂点を結ぶ全単位の円柱を作る。
方針：join の円柱比較を前合成し、図式変数を curry する。
規約：両端の全関手を厳密に保持する。
使われ方：有限余積関手の随伴と指定比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の K の円柱を右頂点が一点の join へ写す。
方針：一点変数を定値にして既存の join 円柱比較を使う。
規約：区間の始点は元の K、終点は指定右頂点。
使われ方：全余錐族の単位。 -/
def coconeUnitCylinder (K : SSet.{u}) : K ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] :=
  lift (𝟙 _) (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap K Δ[0]

/-- 概要：余錐単位円柱の始端は元の左包含。
方針：join 円柱の始端公式を使う。
規約：元の全写像の等式。
使われ方：単位の始端認証。 -/
lemma coconeUnitCylinder_zero (K : SSet.{u}) :
    SSet.ι₀ ≫ coconeUnitCylinder K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] := by
  have h : SSet.ι₀ (X := K) ≫ lift (𝟙 _)
      (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) =
      lift (𝟙 K) (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) ≫
        (SSet.ι₀ ▷ (Δ[0] : SSet.{u})) := by rfl
  rw [coconeUnitCylinder, ← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_zero,
    ← Category.assoc, lift_fst, Category.id_comp]

/-- 概要：余錐単位円柱の終端は指定右頂点への定値写像。
方針：join 円柱の終端公式を使う。
規約：元の指定右頂点を保つ。
使われ方：単位の終端認証。 -/
lemma coconeUnitCylinder_one (K : SSet.{u}) :
    SSet.ι₁ ≫ coconeUnitCylinder K =
      SSet.const (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))) := by
  have h : SSet.ι₁ (X := K) ≫ lift (𝟙 _)
      (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) =
      lift (𝟙 K) (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) ≫
        (SSet.ι₁ ▷ (Δ[0] : SSet.{u})) := by rfl
  rw [coconeUnitCylinder, ← Category.assoc, h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_one,
    ← Category.assoc, lift_snd, SSet.const_comp]
  rfl

/-- 概要：図式変数・族変数・区間を単位円柱に合わせて並べ替える。
方針：直積の三座標を移す。
規約：族変数を全次数で同時に保持する。
使われ方：円柱から関手圏の単位への curry。 -/
def coconeUnitReorder (K A : SSet.{u}) :
    K ⊗ (A ⊗ (Δ[1] : SSet.{u})) ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ A where
  app _ := ↾fun z ↦ ((z.1, z.2.2), z.2.1)
  naturality {_ _} _ := rfl

/-- 概要：全余錐族を元の図式から定値頂点への全円柱にする。
方針：円柱比較と全余錐評価を合成し K を curry する。
規約：パラメータ族の全単体を保持する。
使われ方：余極限関手の全単位。 -/
def coconeFunctorUnitPrism {K A X : SSet.{u}}
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).obj X) : A ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X :=
  curry (coconeUnitReorder K A ≫ (coconeUnitCylinder K ▷ A) ≫ uncurry s)

/-- 概要：全余錐族の単位円柱の始端は元の図式の族。
方針：uncurry して座標交換と始端公式を使う。
規約：全関手の厳密な等式。
使われ方：単位の元の図式条件。 -/
lemma coconeFunctorUnitPrism_zero {K A X : SSet.{u}}
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).obj X) :
    SSet.ι₀ ≫ coconeFunctorUnitPrism s = s ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0])).app X := by
  apply uncurry_injective
  rw [uncurry_natural_left, coconeFunctorUnitPrism, uncurry_curry, uncurry_pre_app]
  have h : (K ◁ SSet.ι₀ (X := A)) ≫ coconeUnitReorder K A = SSet.ι₀ ▷ A := rfl
  rw [← Category.assoc, ← Category.assoc, h, ← comp_whiskerRight, coconeUnitCylinder_zero]

/-- 概要：全余錐族の単位円柱の終端は頂点族の定値関手。
方針：uncurry して終端公式を使い、定値前合成を評価に戻す。
規約：元の指定右頂点族を保持する。
使われ方：余極限関手と定値関手の合成。 -/
lemma coconeFunctorUnitPrism_one {K A X : SSet.{u}}
    (s : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0])).obj X) :
    SSet.ι₁ ≫ coconeFunctorUnitPrism s =
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0])) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_constantFunctorMap]
  apply uncurry_injective
  rw [uncurry_natural_left, coconeFunctorUnitPrism, uncurry_curry, uncurry_pre_app]
  have h : (K ◁ SSet.ι₁ (X := A)) ≫ coconeUnitReorder K A = SSet.ι₁ ▷ A := rfl
  rw [← Category.assoc, ← Category.assoc, h, ← comp_whiskerRight, coconeUnitCylinder_one]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
