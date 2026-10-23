module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.F2.Ind.FullCoconeLift
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：同じ Indκ の小さい κ-filtered 余極限を前層内で構成し、包含で保存・検出する。
方針：元の前層余極限の頂点の閉性を使って全余錐を持ち上げ、同じ余錐の反映と一意性を使う。
規約：元の図式・全余錐を保持。κ-filtered 表示や密度は仮定しない。
使われ方：F2N-2(b)、後続の κ-連続な延長の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C I : SSet.{u}} [Quasicategory C] [Quasicategory I]
  [IsKappaFiltered κ I] (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ IndInfinity κ C)

/-- 同じ前層内の κ-filtered 余極限を、元の全余錐を保って Indκ 内へ持ち上げる。 -/
lemma ind_exists_colimitCone : ∃ c : JoinCocone D,
    IsColimitCone c ∧ IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C) c) := by
  obtain ⟨c, hc, _⟩ := presheafInfinity_exists_colimitCone (D ≫ indInclusionPresheaf κ C)
  have hp : IsIndVertex κ C c.vertex :=
    isIndVertex_kappaColimitClosed κ C I (D ≫ indInclusionPresheaf κ C) c hc
      (fun i ↦ fullSubcomplexOnVertices_vertex (D.app (Opposite.op ⦋0⦌) (ULift.up i)))
  let d := fullCoconeLift (IsIndVertex κ C) D c hp
  refine ⟨d, fullCoconeLift_isColimit _ _ _ _ hc, ?_⟩
  change IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices _ (IsIndVertex κ C)).ι d)
  rw [fullCoconeLift_inclusion]
  exact hc

/-- 元の Indκ 内の任意の小さい κ-filtered 図式は余極限を持つ。 -/
lemma ind_hasColimit : HasColimit D := by
  obtain ⟨c, hc, _⟩ := ind_exists_colimitCone κ D
  exact ⟨c, hc⟩

omit [Quasicategory I] [IsKappaFiltered κ I] in
/-- 同じ全部分包含は元の全余錐の余極限性を反映する。 -/
lemma ind_isColimit_of_inclusion (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C) c)) : IsColimitCone c :=
  isColimitCone_of_fullInclusion (IsIndVertex κ C) c hc

/-- Indκ 内の同じ κ-filtered 余極限全余錐は、元の前層への包含で余極限となる。 -/
lemma ind_inclusion_isColimit (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C) c) := by
  obtain ⟨d, hd, hdi⟩ := ind_exists_colimitCone κ D
  have e := VertexIso.map (colimitConeIso d c hd hc)
    (sliceUnderPostcomp D (indInclusionPresheaf κ C))
  exact hdi.of_vertexIso e

/-- 元の小さい κ-filtered 図式の全余錐の余極限性は、同じ包含により保存・検出される。 -/
lemma ind_isColimit_iff_inclusion (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C) c) :=
  ⟨ind_inclusion_isColimit κ D c, ind_isColimit_of_inclusion κ D c⟩

end SerrePositivity.InfinityCategories.F2.Ind
