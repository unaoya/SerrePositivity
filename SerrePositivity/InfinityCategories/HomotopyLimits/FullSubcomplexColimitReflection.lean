module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexVertexExtension
public import SerrePositivity.InfinityCategories.Core.JoinVertexSurjectivity
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute

/-!
概要：全部分複体の元の余錐が周囲で余極限なら、その同じ余錐は内部でも余極限。
方針：周囲の coslice 境界充填を取り、頂点を被覆する join 境界から元の部分複体へ戻す。
規約：元の図式・余錐・境界の全写像を保持する。モデル構造や新たな存在仮定は不要。
使われ方：元の P_Σ の sifted 余極限余錐の内部での普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全部分複体への余錐の、周囲での余極限性を同じ内部余錐へ反映する。 -/
lemma isColimitCone_of_fullSubcomplex {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    {r : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})} (c : JoinCocone r)
    (hc : IsColimitCone (F1B.kanPostcomposeCocone (fullSubcomplexOnVertices X P).ι c)) :
    IsColimitCone c := by
  intro n b hb
  let inclusion := (fullSubcomplexOnVertices X P).ι
  let b' := b ≫ sliceUnderPostcomp r inclusion
  have hb' : boundaryVertex n 0 ≫ b' =
      SSet.yonedaEquiv.symm (F1B.kanPostcomposeCocone inclusion c) := by
    dsimp only [b']
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hc n b' hb'
  have hboundary : joinMap (𝟙 K) (SSet.boundary (n + 1)).ι ≫ sliceUnderUncurry F =
      sliceUnderUncurry b ≫ inclusion := by
    rw [← sliceUnderUncurry_precomp, hF]
    exact sliceUnderUncurry_postcomp b inclusion
  obtain ⟨L, hLboundary, hLimage⟩ := fullSubcomplex_vertex_extension P _
    (DGNerve.joinMap_vertices_surjective _ _ (fun z => ⟨z, rfl⟩)
      (DGNerve.boundary_vertices_surjective n))
    (sliceUnderUncurry b) (sliceUnderUncurry F) hboundary
  have hfixed : joinInl K (Δ[n + 1] : SSet.{u}) ≫ L = r := by
    apply (cancel_mono inclusion).1
    rw [Category.assoc, hLimage]
    exact sliceUnderUncurry_fixed F
  refine ⟨sliceUnderCurry L hfixed, ?_⟩
  apply sliceUnderUncurry_injective r
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
  exact hLboundary

end SerrePositivity.InfinityCategories.HomotopyLimits
