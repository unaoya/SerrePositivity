module

public import SerrePositivity.KST.Spectra.PointedHomotopyLimitInvariance
public import SerrePositivity.KST.Spectra.KanCompositeCancellation
public import Mathlib.CategoryTheory.Comma.Basic

/-!
## 概要
一般形状の増強から L9 の実点つき Bousfield–Kan end への指定比較。
## 方針
元の点つき錐を忘れた実際の錐に N の比較射を適用し、基点と自然性を保つ。
## 規約
模型圏の仮定を使わない。空間側の π_* と Sp の整数次数の π_* を区別する。
## 使われ方
論文 補題 3.2・3.3。τ 位相の層論を実 end の Čech 計算へ置換する主経路。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.KST.Spectra


namespace SerrePositivity.KST.Descent.Main

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (I : Type u) [SmallCategory I]

/-- 概要：一般形状の点つき増強図式（補題 3.2）。
方針：元と指定増強を定数関手からの comma 圏に保持する。
規約：形状は係数と同じ宇宙に置く。使われ方：実 homotopy limit の比較の定義域。 -/
abbrev AugmentedLimitDiagram :=
  Comma (Functor.const I : PointedSimplicialSet.{u} ⥤ (I ⥤ PointedSimplicialSet.{u})) (𝟭 _)

variable {I}

/-- 概要：点つき指定増強の基礎の錐（補題 3.2）。
方針：comma の指定成分をそのまま忘却する。
規約：頂点と全成分を取り替えない。使われ方：N の実 BK 比較への入力。 -/
def underlyingAugmentationCone (A : AugmentedLimitDiagram I) :
    Cone (A.right ⋙ PointedSimplicialSet.forget) where
  pt := A.left.right
  π := {
    app i := (A.hom.app i).right
    naturality i j f := by
      have h := congrArg (fun g ↦ g.right) (A.hom.naturality f)
      change 𝟙 _ ≫ (A.hom.app j).right =
        (A.hom.app i).right ≫ (A.right.map f).right
      change (A.hom.app j).right =
        (A.hom.app i).right ≫ (A.right.map f).right at h
      exact (Category.id_comp _).trans h }

/-- 概要：一般形状の実点つき homotopy limit への指定比較（補題 3.2）。
方針：元の錐の BK 比較に、基点の錐に関する自然性を添える。
規約：同型を別途選択して比較射と呼ばない。使われ方：添字変更・細分の指定射。 -/
def homotopyLimitComparison (A : AugmentedLimitDiagram I) :
    A.left ⟶ PointedHomotopyLimit.obj A.right :=
  Under.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (underlyingAugmentationCone A)) (by
    change A.left.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (underlyingAugmentationCone A) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (PointedHomotopyLimit.basepointCone A.right)
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
      (PointedHomotopyLimit.basepointCone A.right) (underlyingAugmentationCone A)
      A.left.hom (𝟙 _) (fun i ↦ by
        change A.left.hom ≫ (A.hom.app i).right = (A.right.obj i).hom ≫ 𝟙 _
        rw [Under.w, Category.comp_id]
        rfl)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_id, Category.comp_id] using h)

/-- 概要：実 BK 比較は増強元と係数の同時変更に自然（補題 3.2）。
方針：N の重み付き比較の自然性に comma 射の可換性を渡す。
規約：係数の Kan 性は不要。使われ方：細分で指定射を追跡する。 -/
theorem homotopyLimitComparison_naturality {A B : AugmentedLimitDiagram I} (f : A ⟶ B) :
    f.left ≫ homotopyLimitComparison B =
      homotopyLimitComparison A ≫ PointedHomotopyLimit.map f.right := by
  apply Under.UnderMorphism.ext
  change f.left.right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (underlyingAugmentationCone B) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (underlyingAugmentationCone A) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
          (Functor.whiskerRight f.right PointedSimplicialSet.forget)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)
    (underlyingAugmentationCone A) (underlyingAugmentationCone B) f.left.right
    (Functor.whiskerRight f.right PointedSimplicialSet.forget) (fun i ↦ by
      have h := congrArg (fun g ↦ (g.app i).right) f.w
      exact h)

/-- 概要：一般形状の指定比較による空間側の降下条件（補題 3.2）。
方針：実 BK end の Kan 性と実際の比較射を使う。
規約：増強元と各係数に Kan 性を仮定し、Sp の全整数次数への接続は別に行う。
使われ方：主経路の一般形状の細分・添字変更。 -/
def HasHomotopyLimitDescent (A : AugmentedLimitDiagram I) [KanComplex A.left.right]
    [∀ i, KanComplex (A.right.obj i).right] : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (homotopyLimitComparison A).right

/-- 概要：元と各段の π_* 同型は指定 BK 降下を保存し反映する（補題 3.2）。
方針：実 end の同型保存と指定比較の自然な正方形で合成を消去する。
規約：各係数の Kan 性と元の基点を使う。使われ方：一般形状の細分比較。 -/
theorem hasHomotopyLimitDescent_iff_of_stagewise_piIsomorphism
    {A B : AugmentedLimitDiagram I} [KanComplex A.left.right] [KanComplex B.left.right]
    [∀ i, KanComplex (A.right.obj i).right] [∀ i, KanComplex (B.right.obj i).right]
    (f : A ⟶ B) (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.left.right)
    (hstage : ∀ i, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.right.app i).right) :
    HasHomotopyLimitDescent A ↔ HasHomotopyLimitDescent B := by
  have hmap := PointedHomotopyLimit.map_piIsomorphism f.right hstage
  have hsquare := congrArg (fun g ↦ g.right) (homotopyLimitComparison_naturality f)
  change f.left.right ≫ (homotopyLimitComparison B).right =
    (homotopyLimitComparison A).right ≫ (PointedHomotopyLimit.map f.right).right at hsquare
  constructor
  · intro hA
    have hcomp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.comp hA hmap
    rw [← hsquare] at hcomp
    exact KanPiIsomorphism.cancel_left_atVertex hf hcomp
      (PointedSimplicialSet.basepoint A.left)
  · intro hB
    have hcomp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.comp hf hB
    rw [hsquare] at hcomp
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hcomp hmap

end SerrePositivity.KST.Descent.Main
