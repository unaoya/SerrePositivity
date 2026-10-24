module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarDegreeComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarInputColimit
public import SerrePositivity.InfinityCategories.F2.Presentable.PointKanExtension

/-!
概要：元の前層を表現可能小余積の単体的図式の幾何学的実現として表示する。
方針：初頂点で展開した密度余極限と、次数に沿う左 Kan 延長の余極限を比較する。
規約：元の前層と同じ bar 図式を使い、全関手の同値として頂点を比較する。
使われ方：P_Σ の simplicial Ind 表示と filtered／幾何学的実現による生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 概要：同じ単体的 bar 図式の幾何学的実現は元の前層と同値。
方針：二つの全余極限を、構成した全左 Kan 延長の普遍性で比較する。
規約：元の前層の関手頂点との頂点同型を与える。
使われ方：表現可能前層の小余積による単体的生成表示。 -/
lemma presheafBarObject_realization :
    ∃ d : JoinCocone (presheafBarObject F),
      IsColimitCone d ∧ Nonempty (VertexIso d.vertex (functorVertex F)) := by
  obtain ⟨c, hc, hv⟩ := presheafBarInput_colimitPresentation F
  obtain ⟨d, hd⟩ := presheafInfinity_hasColimit (presheafBarObject F)
  let e := F2.Presentable.leftKan_colimitVertexIso
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (presheafBarDegree F)))
    (presheafBarUnit F) (presheafBarUnit_isLeftKanExtension F) c hc d hd
  exact ⟨d, hd, ⟨e ≪≫ eqToIso (congrArg HomotopyCategory.mk hv)⟩⟩

/-- 概要：各 bar 次数の離散図式の全対象は表現可能前層である。
方針：同じファイバーの包含後に元の入力図式の頂点公式を使う。
規約：元の頂点の厳密な等式で表現可能性を与える。
使われ方：各 bar 項の小余積の生成対象の確認。 -/
lemma presheafBarDegreeDiagram_representable
    (n : ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ))
    (s : (presheafBarSimplexFamily F).obj n) :
    ∃ x : C _⦋0⦌,
      ((SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (presheafBarFiberInclusion F n.objDown.down)) ≫ presheafBarInputDiagram F).app
        (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk s))) =
          functorVertex (representablePresheafInfinity x) := by
  exact ⟨_, presheafBarInputDiagram_vertex F
    ((presheafBarFiberInclusion F n.objDown.down).obj (Discrete.mk s))⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
