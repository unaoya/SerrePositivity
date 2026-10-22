module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

/-! # 同じ点つき実押し出しによる anodyne 性の保存
概要：同じ点つき実押し出しは、基礎単体集合の anodyne 射を anodyne 射へ送る。
方針：忘却の連結余極限保存と anodyne 類の押し出し閉性を使う。
規約：モデル圏引数を導入しない。使われ方：同じ実写像円柱の射影の弱同値性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 同じ点つき実押し出しによる基礎 anodyne 射の保存。 -/
lemma pointedIsPushout_anodyne_right
    {A B C D : PointedSimplicialSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {l : B ⟶ D} {r : C ⟶ D} (h : IsPushout f g l r) (hf : anodyneExtensions f.right) :
    anodyneExtensions r.right := by
  have hs := (Under.forget (𝟙_ SSet.{u})).map_isPushout h
  change IsPushout f.right g.right l.right r.right at hs
  exact anodyneExtensions.of_isPushout hs.flip hf

/-- 同じ点つき押し出しの右包含は、左脚の基礎 anodyne 性を保つ。 -/
lemma pointedPushout_inr_anodyne {A B C : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (hf : anodyneExtensions f.right) :
    anodyneExtensions (pushout.inr f g).right :=
  pointedIsPushout_anodyne_right (IsPushout.of_hasPushout f g) hf

end SerrePositivity.KST.SConstruction
