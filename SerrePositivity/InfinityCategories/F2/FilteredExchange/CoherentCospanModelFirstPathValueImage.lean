module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanCommonPathClasses
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelKanValuePath

/-!
概要：模型の第一置換 path の像を、元の頂点の値の指定 path へ戻す。
方針：二つの円柱の全時刻の一致を後合成し、同じ指定同型の類を回収する。
規約：端点は全円柱の両端評価から比較。使われ方：左の定値切断収縮の像の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "f" => continuousKanReplacement.map (coherentTransformationTotalMap X Z C.fromLeft)
local notation "g" => continuousKanReplacement.map (coherentTransformationTotalMap Y Z C.fromRight)
local notation "eF" => eqToHom (coherentDiagramTotalVertex_object F)
local notation "w" => eqToHom (Eq.symm (coherentDiagramTotalVertex_object Z))
local notation "bM" => eF ≫ coherentCospanConeKanComparison F X Y Z C ≫
  pullback.fst (intervalReplacementEndpoint f) g

/-- 模型の第一置換 path の元の値での指定像は、候補の値の指定 path そのもの。 -/
lemma coherentCospanModelFirstPathValueImage :
    HEq (((intervalReplacementPathIso f).precomp bM).postcomp w)
      (coherentCospanConeValuePathIso F X Y Z C) := by
  have he : intervalReplacementPathIso f =
      functorIsoOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f) := by
    apply Iso.ext
    rfl
  have hi := homotopyIso_heq_of_h_eq
    (functorHomotopyPostcomp
      (functorHomotopyPrecomp (intervalReplacementCanonicalPathHomotopy f) bM) w)
    (functorHomotopyPostcomp
      (functorHomotopyPrecomp (coherentCospanConeKanPathHomotopy F X Y Z C) eF) w)
    (by apply SSet.hom_ext; intro n; rfl)
  rw [homotopyIso_postcomp, homotopyIso_precomp,
    homotopyIso_postcomp, homotopyIso_precomp, ← he] at hi
  have hv : HEq (coherentCospanConeKanValuePathIso F X Y Z C)
      (((functorIsoOfSimplicialHomotopy
        (coherentCospanConeKanPathHomotopy F X Y Z C)).precomp eF).postcomp w) :=
    functorIsoOfEq_heq _ _ _
  rw [coherentCospanConeKanValuePathIso_eq] at hv
  exact hi.trans hv.symm

end SerrePositivity.InfinityCategories.F2
