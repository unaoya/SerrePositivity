module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.GluedFiberDetection

/-!
概要：有限模型の指定部分 path を、底の構成ではそのパラメータへ潰す。
方針：部分 path の射と path 変数を忘れる射の押し出しを取る。
規約：全空間の模型は変えず、底の収縮を選ぶ形状だけを変える。
使われ方：指定部分 path 上で path 方向に定値な共通底の収縮を得る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {A M B : SSet.{u}} (k : (Δ[1] : SSet.{u}) ⊗ A ⟶ M)

/-- 概要：底で指定部分 path の区間変数を忘れる形状。
方針：部分 path の射と第二射影の押し出し。
規約：元の模型 M は第一脚で入る。使われ方：境界に整合する底の共通収縮。 -/
def pathCollapseBase : SSet.{u} := pushout k (snd (Δ[1] : SSet.{u}) A)

/-- 概要：有限模型と有限部分パラメータから作る底の形状は有限。
方針：有限押し出し。規約：k に単射性は不要。使われ方：filtered な底での収縮。 -/
instance pathCollapseBase_finite [A.Finite] [M.Finite] : (pathCollapseBase k).Finite :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_pushout k (snd (Δ[1] : SSet.{u}) A)

/-- 概要：元の模型から底の押し出し形状への射。
方針：押し出しの第一脚。規約：全模型。使われ方：選んだ収縮の元の模型への制限。 -/
def pathCollapseBaseModel : M ⟶ pathCollapseBase k :=
  pushout.inl k (snd (Δ[1] : SSet.{u}) A)

/-- 概要：部分パラメータから底の押し出し形状への射。
方針：押し出しの第二脚。規約：path 変数を持たない。使われ方：境界輸送の底の収縮。 -/
def pathCollapseBaseParameter : A ⟶ pathCollapseBase k :=
  pushout.inr k (snd (Δ[1] : SSet.{u}) A)

/-- 概要：指定部分 path は押し出し形状でパラメータのみに因子分解する。
方針：押し出しの可換式。規約：厳密な式。使われ方：収縮の全時刻での path 定値性。 -/
lemma pathCollapseBase_condition :
    k ≫ pathCollapseBaseModel k = snd (Δ[1] : SSet.{u}) A ≫ pathCollapseBaseParameter k :=
  pushout.condition

/-- 概要：指定部分 path 上で定値な底射は押し出し形状からの射を与える。
方針：二つの底射を貼る。規約：元の底射を保持。使われ方：共通底の収縮の入力。 -/
def pathCollapseBaseMap (r : M ⟶ B) (a : A ⟶ B)
    (h : k ≫ r = snd (Δ[1] : SSet.{u}) A ≫ a) : pathCollapseBase k ⟶ B :=
  pushout.desc r a h

/-- 概要：押し出しからの底射の模型上の制限は元の底射。
方針：第一脚の式。規約：厳密な一致。使われ方：元の模型の輸送。 -/
lemma pathCollapseBaseMap_model (r : M ⟶ B) (a : A ⟶ B)
    (h : k ≫ r = snd (Δ[1] : SSet.{u}) A ≫ a) :
    pathCollapseBaseModel k ≫ pathCollapseBaseMap k r a h = r := pushout.inl_desc _ _ _

/-- 概要：押し出しからの底射の部分パラメータ上の制限は元の底射。
方針：第二脚の式。規約：厳密な一致。使われ方：指定境界の輸送。 -/
lemma pathCollapseBaseMap_parameter (r : M ⟶ B) (a : A ⟶ B)
    (h : k ≫ r = snd (Δ[1] : SSet.{u}) A ≫ a) :
    pathCollapseBaseParameter k ≫ pathCollapseBaseMap k r a h = a := pushout.inr_desc _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
