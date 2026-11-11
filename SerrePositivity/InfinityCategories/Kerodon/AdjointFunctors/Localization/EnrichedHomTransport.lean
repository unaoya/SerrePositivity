module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 豊穣 Hom と underlying 射の元の対象等式による移送

概要：一定単体写像の終域 Hom の表示変更を underlying 射の異種等式へ移す。
方針：元の対象の等式を消去し、同じ元の単体写像を回収する。
規約：対象表示の等式を保持し、新しい同型を選ばない。
使われ方：二つの自由部分の対象表示を含む元の関手の同定。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {D : Type uD} [EnrichedCategory SSet.{u} D]

def homMap {X X' Y Y' : D} (hX : X = X') (hY : Y = Y') :
    (X ⟶[SSet.{u}] Y) ⟶ X' ⟶[SSet.{u}] Y' :=
  eqToHom (congrArg₂ (fun A B : D => A ⟶[SSet.{u}] B) hX hY)

lemma point_homOf_heq {X X' Y Y' : D} (hX : X = X') (hY : Y = Y')
    (p : 𝟙_ SSet.{u} ⟶ X ⟶[SSet.{u}] Y) :
    HEq (ForgetEnrichment.homOf SSet.{u} (p ≫ homMap hX hY))
      (ForgetEnrichment.homOf SSet.{u} p) := by
  cases hX
  cases hY
  change HEq (ForgetEnrichment.homOf SSet.{u} (p ≫ 𝟙 _))
    (ForgetEnrichment.homOf SSet.{u} p)
  rw [Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
