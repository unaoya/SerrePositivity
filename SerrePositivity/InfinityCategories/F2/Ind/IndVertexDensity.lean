module

public import SerrePositivity.InfinityCategories.F2.Ind.IndDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.NativeFilteredPreservation

/-!
概要：Indκ の指定頂点そのものを持つ、元の小さい元の圏上の κ-filtered 密度余錐。
方針：元の前層頂点を関手へ戻し、同じ密度余錐の頂点を全部分包含の単射性で同定する。
規約：元の頂点と元の全余錐を保つ。対象ごとに同値な別表示を選び直さない。
使われ方：保存関手の値と、Yoneda による制限の可逆性の検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌)

/-- 元の Indκ 頂点が表す、同じ前層の実際の関手。 -/
def indVertexPresheaf : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u} :=
  (presheafInfinityObjectEquiv C).symm v.val

lemma indVertexPresheaf_vertex : functorVertex (indVertexPresheaf κ v) = v.val :=
  (presheafInfinityObjectEquiv C).apply_symm_apply v.val

lemma indVertexPresheaf_mem : IsIndVertex κ C (functorVertex (indVertexPresheaf κ v)) :=
  (indVertexPresheaf_vertex κ v).symm ▸ fullSubcomplexOnVertices_vertex v

/-- 同じ指定 Indκ 頂点の元の元の圏上の密度余錐。 -/
def indVertexDensityCocone : JoinCocone (indDensityDiagram κ (indVertexPresheaf κ v)) :=
  indDensityCocone κ (indVertexPresheaf κ v) (indVertexPresheaf_mem κ v)

lemma indVertexDensityCocone_vertex : (indVertexDensityCocone κ v).vertex = v := by
  apply Subtype.ext
  exact (indDensityCocone_vertex κ (indVertexPresheaf κ v)
    (indVertexPresheaf_mem κ v)).trans (indVertexPresheaf_vertex κ v)

lemma indVertexDensityCocone_isColimit : IsColimitCone (indVertexDensityCocone κ v) :=
  indDensityCocone_isColimit κ (indVertexPresheaf κ v) (indVertexPresheaf_mem κ v)

/-- 同じ指定頂点の元の元の圏は小さい κ-filtered ∞ 圏。 -/
lemma indVertexElements_isKappaFiltered [Fact κ.IsRegular] :
    IsKappaFiltered κ (smallRightUnstraightening (indVertexPresheaf κ v)) :=
  (isIndVertex_functorVertex_iff κ C _).mp (indVertexPresheaf_mem κ v)

/-- 保存関手による元の全密度余錐の像は、同じ指定値の native 余極限。 -/
lemma indVertexDensity_image_isColimit [Fact κ.IsRegular] {D : SSet.{u + 1}}
    (G : IndInfinity κ C ⟶ D) (hG : PreservesSmallKappaFilteredColimits κ G) :
    IsColimitCone (mapJoinCocone G (indVertexDensityCocone κ v)) := by
  have := indVertexElements_isKappaFiltered κ v
  exact hG _ _ _ (indVertexDensityCocone_isColimit κ v)

end SerrePositivity.InfinityCategories.F2.Ind
