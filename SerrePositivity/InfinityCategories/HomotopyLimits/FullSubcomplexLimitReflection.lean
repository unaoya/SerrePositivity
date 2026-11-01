module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexVertexExtension
public import SerrePositivity.InfinityCategories.Core.JoinVertexSurjectivity
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits

/-!
概要：全部分複体の元の錐が周囲で極限なら、その同じ錐は内部でも極限。
方針：周囲の coslice 境界充填を取り、頂点を被覆する join 境界から元の部分複体へ戻す。
規約：元の図式・錐・境界の全写像を保持する。モデル構造や新たな存在仮定は不要。
使われ方：元の 反映部分圏 の sifted 極限錐の内部での普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：全部分複体の錐の極限性を周囲から反映する。
方針：周囲での境界充填を全頂点の被覆で元の部分複体へ戻す。
規約：任意の形状を扱い、充填の全写像を保持する。
使われ方：反映部分圏の小極限。 -/
lemma isLimitCone_of_fullSubcomplex {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    {r : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})} (c : JoinCone r)
    (hc : IsLimitCone (mapJoinCone (fullSubcomplexOnVertices X P).ι c)) :
    IsLimitCone c := by
  intro n b hb
  let inclusion := (fullSubcomplexOnVertices X P).ι
  let b' := b ≫ sliceOverPostcomp r inclusion
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ b' =
      SSet.yonedaEquiv.symm (mapJoinCone inclusion c) := by
    dsimp only [b']
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hc n b' hb'
  have hboundary : joinMap (SSet.boundary (n + 1)).ι (𝟙 K) ≫ sliceOverUncurry F =
      sliceOverUncurry b ≫ inclusion := by
    rw [← sliceOverUncurry_precomp, hF]
    exact sliceOverUncurry_postcomp b inclusion
  obtain ⟨L, hLboundary, hLimage⟩ := fullSubcomplex_vertex_extension P _
    (DGNerve.boundaryJoin_vertices_surjective n K)
    (sliceOverUncurry b) (sliceOverUncurry F) hboundary
  have hfixed : joinInr (Δ[n + 1] : SSet.{u}) K ≫ L = r := by
    apply (cancel_mono inclusion).1
    rw [Category.assoc, hLimage]
    exact sliceOverUncurry_fixed F
  refine ⟨sliceOverCurry L hfixed, ?_⟩
  apply sliceOverUncurry_injective r
  rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
  exact hLboundary

end SerrePositivity.InfinityCategories.HomotopyLimits
