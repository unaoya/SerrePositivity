module
public import SerrePositivity.KST.SConstruction.PointedSmashPushoutAnodyne
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # 任意の点つき対象との同じ右 smash による anodyne 保存
概要：元の基礎 anodyne 射を右 smash しても、同じ基礎 anodyne 類に入る。
方針：点からの基点射との smash pushout-product を使い、零対象側の同型で源を戻す。
規約：Kan 性や ModelCategory 引数なし。使われ方：同じ円柱端点の弱比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet PointedObject

/-- 元の点つき対象の基点射は、基礎単体集合上の単射。 -/
lemma pointedFromPoint_mono (X : PointedSimplicialSet.{u}) : Mono (fromPoint X).right := by
  change Mono X.hom
  exact CartesianMonoidalCategory.isTerminalTensorUnit.mono_from _

/-- 同じ元の一点との smash は零対象。 -/
lemma pointedSmashPoint_isZero (A : PointedSimplicialSet.{u}) :
    IsZero (A ⊗ (point : PointedSimplicialSet.{u})) :=
  CategoryTheory.Functor.map_isZero (tensorLeft A) point_isZero

/-- 点との smash の任意の元の射は、零対象間の同型。 -/
lemma pointedSmashPointMap_isIso {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) :
    IsIso (smashMap f (𝟙 (point : PointedSimplicialSet.{u}))) := by
  exact ⟨⟨0, (pointedSmashPoint_isZero A).eq_of_src _ _,
    (pointedSmashPoint_isZero B).eq_of_src _ _⟩⟩

/-- 同じ実 smash 境界の右包含は、点からの基点射の場合に同型。 -/
lemma pointedSmashBoundaryFromPoint_isIso {A B : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (X : PointedSimplicialSet.{u}) :
    IsIso (smashBoundaryInr f (fromPoint X)) := by
  let _ : IsIso (smashMap f (𝟙 (point : PointedSimplicialSet.{u}))) :=
    pointedSmashPointMap_isIso f
  change IsIso (pushout.inr (smashMap f (𝟙 (point : PointedSimplicialSet.{u}))) _)
  infer_instance

/-- 元の基礎 anodyne 射は、任意の点つき右因子との同じ smash で anodyne。 -/
lemma pointedWhiskerRight_anodyne {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : anodyneExtensions f.right) (X : PointedSimplicialSet.{u}) :
    anodyneExtensions (f ▷ X).right := by
  let _ : Mono (fromPoint X).right := pointedFromPoint_mono X
  let _ : IsIso (smashBoundaryInr f (fromPoint X)) := pointedSmashBoundaryFromPoint_isIso f X
  have h := pointedSmashPushoutProduct_anodyne f (fromPoint X) hf
  let _ : IsIso (smashBoundaryInr f (fromPoint X)).right :=
    (Under.forget (𝟙_ SSet.{u})).map_isIso _
  have hi : anodyneExtensions (smashBoundaryInr f (fromPoint X)).right :=
    anodyneExtensions.of_isIso _
  have hc := anodyneExtensions.comp_mem _ _ hi h
  change anodyneExtensions (smashMap f (𝟙 X)).right
  exact (congrArg (fun q => anodyneExtensions q.right)
    (smashBoundaryInr_smashPushoutProduct f (fromPoint X))).mp hc

end SerrePositivity.KST.SConstruction
