module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：二つの連続 Kan 置換の単位の直積は anodyne であり弱ホモトピー同値。
方針：各単位の anodyne 性を左右の直積で保存し、二射を合成する。
規約：元の二対象の Kan 性は不要。
使われ方：全空間の積から Kan 模型の積への実際の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二つの単位の直積は anodyne。
方針：右と左の直積で保存した二つの anodyne 射を合成する。
規約：元の指定単位の直積。使われ方：全空間積の Kan 比較。 -/
lemma continuousKanProductUnit_anodyne (E D : SSet.{u}) :
    anodyneExtensions (continuousKanReplacementUnit.app E ⊗ₘ
      continuousKanReplacementUnit.app D) := by
  rw [tensorHom_def]
  exact anodyneExtensions.comp_mem _ _
    ((continuousKanReplacementUnit_anodyne E).whiskerRight D)
    ((continuousKanReplacementUnit_anodyne D).whiskerLeft (continuousKanReplacement.obj E))

/-- 概要：二つの全空間から各 Kan 模型の積への単位は弱ホモトピー同値。
方針：anodyne 性から全 Kan 標的への前合成同値を取る。
規約：元の対象は任意。使われ方：積比較の単位の可換式による消去。 -/
lemma continuousKanProductUnit_isWeakHomotopyEquivalence (E D : SSet.{u}) :
    IsWeakHomotopyEquivalence (continuousKanReplacementUnit.app E ⊗ₘ
      continuousKanReplacementUnit.app D) := by
  intro Z _
  exact (HomotopyLimits.homotopyEquivalence_pre_of_anodyne _
    (continuousKanProductUnit_anodyne E D) Z).mapPiZero_bijective

end SerrePositivity.InfinityCategories.F2
