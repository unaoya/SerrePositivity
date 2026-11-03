module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanModelKanPathClass
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCospanConeRelativeValuePath

/-!
概要：元の模型 Kan 比較の指定 path を元の余極限頂点の値の間へ移す。
方針：頂点表示を前後合成し、元の二合成の式で端点を揃える。
規約：既存候補の指定可換同型の値を保持。使われ方：native 比較候補への最終比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight

/-- 元の Kan 比較の指定 path を元の頂点の値の二合成の間に表示する。 -/
def coherentCospanConeKanValuePathIso :
    FunctorIso (coherentTotalVertexMap F X cl ≫ coherentTotalVertexMap X Z cf)
      (coherentTotalVertexMap F Y cr ≫ coherentTotalVertexMap Y Z cg) :=
  functorIsoOfEq
    (((functorIsoOfSimplicialHomotopy (coherentCospanConeKanPathHomotopy F X Y Z C)).precomp
      (eqToHom (coherentDiagramTotalVertex_object F))).postcomp
        (eqToHom (coherentDiagramTotalVertex_object Z).symm))
    (coherentTotalVertexMap_comp F X Z cl cf) (coherentTotalVertexMap_comp F Y Z cr cg)

/-- 元の模型 Kan 比較の指定 path は既存候補の元の値の指定 path に厳密に一致する。 -/
lemma coherentCospanConeKanValuePathIso_eq :
    coherentCospanConeKanValuePathIso F X Y Z C = coherentCospanConeValuePathIso F X Y Z C := by
  unfold coherentCospanConeKanValuePathIso
  rw [coherentCospanConeKanPathHomotopy_iso]
  rw [← coherentCospanConeRelativeValuePathIso_eq]
  unfold coherentCospanConeRelativeValuePathIso
  rw [coherentTotalVertexPathIso_eq_whisker]

end SerrePositivity.InfinityCategories.F2
