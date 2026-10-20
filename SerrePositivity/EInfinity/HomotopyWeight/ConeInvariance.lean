module

public import SerrePositivity.EInfinity.HomotopyWeight.ConeLifting
public import SerrePositivity.EInfinity.HomotopyWeight.KanDiagramBrown

/-!
# Kan 値図式の射影重みの錐のホモトピー不変性

概要：Hovey §5.4 の射影 cofibrant 重みの錐は各値の anodyne 局所化同値を保つ。
方針：境界の右類の保存を Kan 値図式の自然な Brown 分解へ渡す。
規約：単体集合とその図式圏の完全なモデル構造は仮定しない。
使われ方：始域 frame と右 frame の比較を重み付き錐へ移す。
-/

@[expose] public section

noncomputable section

universe u v w

namespace SerrePositivity.EInfinity.HomotopyWeight

open CategoryTheory Limits
open SerrePositivity.DiagramModel.WeightedCones
open SerrePositivity.SimplicialModel

variable (K : Type u) [SmallCategory K] (W : K ⥤ SSet.{u})
  (hW : (boundaries K).rlp.llp (initial.to W))

include hW

/-- 概要：射影重みの錐は Kan 値図式の各値の局所化同値を反転する（Hovey §5.4）。
方針：境界の右類の像の収縮と自然な Kan 図式の Brown 分解を使う。
規約：反転先は任意の anodyne を反転する関手でよい。
使われ方：両側の frame の自然な比較の錐を同型へ移す。 -/
lemma coneSpace_map_isIso_of_pointwiseKan {F G : K ⥤ SSet.{u}} (f : F ⟶ G)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    {D : Type v} [Category.{w} D] (L : SSet.{u} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map ((coneSpace K W).map f)) :=
  map_isIso_of_pointwiseKan K (coneSpace K W ⋙ L)
    (fun p hp => coneSpace_map_isIso_of_boundary_rlp K W hW p hp L hL) f hF hG hf

end SerrePositivity.EInfinity.HomotopyWeight
