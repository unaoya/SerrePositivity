module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderSquareForwardEndpoints

/-!
概要：両端が同値である実際の円柱上の四角形の空間。
方針：回収した二つの端点写像を同値の関手空間へ引き戻す。
規約：両端の同値性を全高次単体の部分空間として扱う。
使われ方：prism 中間模型との厳密な同型の比較対象。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：両端が同値である実際の四角形の空間。
方針：両端評価を同値の空間の積へ引き戻す。
規約：始点と終点をともに厳密に指定する。
使われ方：円柱上の表現の具体的な比較対象。 -/
def cylinderEquivalenceSquareSpace {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : SSet.{u + 1} :=
  pullback (lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget f s t))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι K s ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t)

/-- 概要：両端同値の四角形から周囲の固定両端四角形を取り出す。
方針：引き戻しの第一射影。
規約：全空間側と底側の両射を保つ。
使われ方：逆比較の prism の回収。 -/
def cylinderEquivalenceSquareForget {K J : SSet.{u + 1}} [Quasicategory K] [Quasicategory J]
    (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareSpace f s t ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSpace f s t :=
  pullback.fst _ _

/-- 概要：両端同値の四角形の指定した両端の同値を取り出す。
方針：引き戻しの第二射影。
規約：同値の空間の積への射。
使われ方：逆比較の貼り合わせの端点条件。 -/
def cylinderEquivalenceSquareEndpoints {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareSpace f s t ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace K s ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceSpace J t :=
  pullback.snd _ _

/-- 概要：両端同値の四角形の始点は指定した始点同値の包含。
方針：引き戻し条件を第一射影で評価する。
規約：射そのものの等式。
使われ方：逆比較の始点同値への持ち上げ。 -/
lemma cylinderEquivalenceSquareForget_source {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareForget f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t =
      cylinderEquivalenceSquareEndpoints f s t ≫ fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι K s := by
  have h := congrArg (fun w ↦ w ≫ fst _ _) (pullback.condition
    (f := lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget f s t))
    (g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι K s ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t))
  simp only [Category.assoc, lift_fst, tensorHom_fst] at h
  exact h

/-- 概要：両端同値の四角形の終点は指定した終点同値の包含。
方針：引き戻し条件を第二射影で評価する。
規約：射そのものの等式。
使われ方：逆比較の終点の貼り合わせ。 -/
lemma cylinderEquivalenceSquareForget_target {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    cylinderEquivalenceSquareForget f s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget f s t =
      cylinderEquivalenceSquareEndpoints f s t ≫ snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t := by
  have h := congrArg (fun w ↦ w ≫ snd _ _) (pullback.condition
    (f := lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareSource f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cylinderFixedEndpointSquareTarget f s t))
    (g := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι K s ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedPrismSourceEquivalenceι J t))
  simp only [Category.assoc, lift_snd, tensorHom_snd] at h
  exact h

/-- 概要：prism 中間模型から両端同値の実際の四角形への順比較。
方針：端点を保つ順比較を同値の空間への引き戻しへ持ち上げる。
規約：全ての高次 prism を含む実際の空間の射。
使われ方：逆比較との厳密な同型の順方向。 -/
def pointedCylinderEquivalenceSquareMap {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismSpace f s t ⟶ cylinderEquivalenceSquareSpace f s t :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpoints f s t) (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_source]
      rfl
    · simp only [Category.assoc, lift_snd, tensorHom_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap_target]
      rfl)

/-- 概要：順比較を周囲の四角形へ戻すと既存の比較。
方針：引き戻しの第一射影。
規約：厳密な回収。
使われ方：往復の全空間側と底側の検証。 -/
lemma pointedCylinderEquivalenceSquareMap_forget {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderEquivalenceSquareMap f s t ≫ cylinderEquivalenceSquareForget f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pointedCylinderFixedSquareMap f s t := pullback.lift_fst _ _ _

/-- 概要：順比較は指定した両端同値を保つ。
方針：引き戻しの第二射影。
規約：両端の同値の族全体の回収。
使われ方：往復の境界条件の検証。 -/
lemma pointedCylinderEquivalenceSquareMap_endpoints {K J : SSet.{u + 1}}
    [Quasicategory K] [Quasicategory J] (f : K ⟶ J) (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    pointedCylinderEquivalenceSquareMap f s t ≫ cylinderEquivalenceSquareEndpoints f s t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedCylinderPrismEndpoints f s t := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
