module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.TargetInvariance
public import SerrePositivity.EInfinity.FrameHom.SimplexTerminalEquivalence
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpace
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# 分解から自明 fibration への持ち上げ空間の実際の収縮

概要：Low 命題 3.6 の分解の asphericity に使う持ち上げ空間を収縮する。
方針：元の境界の持ち上げ性を同じ fiber へ引き戻し、単射の右類の収縮を使う。
規約：単体集合のモデル構造を仮定せず、元の LiftSpace と射影を保持する。
使われ方：共通比較の右射の分解側の comma 圏の可縮性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uH vH

namespace SerrePositivity.EInfinity.FrameHom.FrameLift

open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (A : SimplexCategory ⥤ C) {X : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  {E B : C} (p : E ⟶ B) [Fibration p] [WeakEquivalence p] (f : X ⟶ B)

include hA in
/-- 概要：元の持ち上げ空間の射影は全単射の右持ち上げ性を持つ（Low 命題 3.6）。
方針：元の Hom の境界右類を fiber の引き戻しへ移す。
規約：単体集合のモデル構造の入力なし。
使われ方：元の持ち上げ空間の収縮。 -/
lemma projection_mono_rlp :
    (MorphismProperty.monomorphisms SSet.{v}).rlp (LiftSpace.projection A a p f) := by
  have h := SSet.rlp_monomorphisms.ge _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.target_boundary_rlp A hA p)
  intro K L i hi
  have : HasLiftingProperty i ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) := h i hi
  exact (IsPullback.of_hasPullback ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p)
    (LiftSpace.point A a f)).hasLiftingProperty i

include hA in
/-- 概要：同じ持ち上げ空間は任意の anodyne 反転関手で点と同型（Low 命題 3.6）。
方針：同じ射影の単射右類から実際の切断と縦の収縮を構成する。
規約：順射は元の fiber の射影の像。
使われ方：持ち上げの反対要素圏の nerve の可縮性。 -/
lemma projection_image_isIso {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (LiftSpace.projection A a p f)) :=
  MonoRightLiftingContraction.image_isIso _ (projection_mono_rlp A a hA p f) L hL

include hA in
/-- 概要：全持ち上げ単体の反対要素圏の元の終射も反転可能（Low 命題 3.6）。
方針：終端 augmentation と同じ fiber 射影を合成し終射の一意性を使う。
規約：零次の持ち上げだけへ制限しない。
使われ方：分解側の asphericity の全次数の入力。 -/
lemma elementsTerminal_image_isIso {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (SSet.stdSimplex.isTerminalObj₀.from
      (nerve (LiftSpace.obj A a p f).Elementsᵒᵖ))) := by
  have : IsIso (L.map (SimplexTerminalNerve.augmentation.app (LiftSpace.obj A a p f))) :=
    SimplexTerminalNerve.augmentation_image_isIso L hL _
  have : IsIso (L.map (LiftSpace.projection A a p f)) :=
    projection_image_isIso A a hA p f L hL
  have h : SimplexTerminalNerve.augmentation.app (LiftSpace.obj A a p f) ≫
      LiftSpace.projection A a p f = SSet.stdSimplex.isTerminalObj₀.from
        (nerve (LiftSpace.obj A a p f).Elementsᵒᵖ) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← h, L.map_comp]
  infer_instance

end SerrePositivity.EInfinity.FrameHom.FrameLift
