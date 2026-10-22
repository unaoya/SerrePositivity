module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # 同じ点つき実押し出しによる基礎単射の保存
概要：点つき圏の実押し出しで、元の基礎単体集合の単射を保存する。
方針：忘却の連結余極限保存と、具体的な境界生成の左持ち上げ類を使う。
規約：モデル圏の instance 仮定を追加しない。使われ方：実写像円柱源比較の単射性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open SSet.modelCategoryQuillen SerrePositivity.SimplicialModel

/-- 同じ点つき実押し出しは、元の基礎単射を単射へ送る。 -/
lemma pointedIsPushout_mono_right
    {A B C D : PointedSimplicialSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {l : B ⟶ D} {r : C ⟶ D} (h : IsPushout f g l r) [Mono f.right] : Mono r.right := by
  have hs := (Under.forget (𝟙_ SSet.{u})).map_isPushout h
  change IsPushout f.right g.right l.right r.right at hs
  have hf : I.rlp.llp f.right := by
    rw [boundaryGenerators_leftClass]
    infer_instance
  have hm := I.rlp.llp.of_isPushout hs.flip hf
  rw [boundaryGenerators_leftClass] at hm
  exact hm

/-- 同じ元の点つき押し出しの右包含は、左脚の基礎単射性を保つ。 -/
lemma pointedPushout_inr_mono {A B C : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : A ⟶ C) [Mono f.right] : Mono (pushout.inr f g).right :=
  pointedIsPushout_mono_right (IsPushout.of_hasPushout f g)

end SerrePositivity.KST.SConstruction
