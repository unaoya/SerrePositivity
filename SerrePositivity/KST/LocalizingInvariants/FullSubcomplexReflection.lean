module

public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Stable.Pointed
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.Core.JoinVertexSurjectivity

/-!
概要：頂点条件の全部分複体は始終対象性と錐の普遍性を反映する。
方針：全頂点を覆う境界上にある延長を、元の全単体を保って部分複体へ制限する。
規約：周囲の安定性は不要。使われ方：通常 pullback の安定性と完全包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FullSubcomplex

variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

lemma extension {A B : SSet.{u}} (j : A ⟶ B)
    (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    (a : A ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) (F : B ⟶ X)
    (h : j ≫ F = a ≫ (fullSubcomplexOnVertices X P).ι) :
    ∃ L : B ⟶ (fullSubcomplexOnVertices X P : SSet.{u}),
      j ≫ L = a ∧ L ≫ (fullSubcomplexOnVertices X P).ι = F := by
  have hv (b : B _⦋0⦌) : P (F.app (Opposite.op ⦋0⦌) b) := by
    obtain ⟨v, rfl⟩ := hj b
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) v
    change F.app _ (j.app _ v) = (a.app _ v).val at he
    rw [he]
    exact fullSubcomplexOnVertices_vertex (a.app _ v)
  refine ⟨fullSubcomplexLift P F hv, ?_, fullSubcomplexLift_ι P F hv⟩
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).1
  rw [Category.assoc, fullSubcomplexLift_ι]
  exact h

lemma reflects_initial (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (hx : IsInitialVertex x.val) : IsInitialVertex x := by
  intro n b hb
  let q := (fullSubcomplexOnVertices X P).ι
  have hb' : boundaryVertex n 0 ≫ (b ≫ q) = SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hb'
  obtain ⟨L, hL, _⟩ := extension P (boundary (n + 1)).ι
    (DGNerve.boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

lemma reflects_terminal (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (hx : IsTerminalVertex x.val) : IsTerminalVertex x := by
  intro n b hb
  let q := (fullSubcomplexOnVertices X P).ι
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hb'
  obtain ⟨L, hL, _⟩ := extension P (boundary (n + 1)).ι
    (DGNerve.boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

lemma reflects_zero (x : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (hx : IsZeroVertex x.val) : IsZeroVertex x :=
  ⟨reflects_initial P x hx.1, reflects_terminal P x hx.2⟩

lemma reflects_limit {K : SSet.{u}}
    {p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})} (c : JoinCone p)
    (hc : IsLimitCone (mapJoinCone (fullSubcomplexOnVertices X P).ι c)) : IsLimitCone c := by
  intro n b hb
  let q := (fullSubcomplexOnVertices X P).ι
  let b' := b ≫ sliceOverPostcomp p q
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ b' =
      SSet.yonedaEquiv.symm (mapJoinCone q c) := by
    dsimp only [b']
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hc n b' hb'
  have hboundary : joinMap (boundary (n + 1)).ι (𝟙 K) ≫ sliceOverUncurry F =
      sliceOverUncurry b ≫ q := by
    rw [← sliceOverUncurry_precomp, hF]
    exact sliceOverUncurry_postcomp b q
  obtain ⟨L, hL, hLq⟩ := extension P _ (DGNerve.boundaryJoin_vertices_surjective n K)
    (sliceOverUncurry b) (sliceOverUncurry F) hboundary
  have hfixed : joinInr (Δ[n + 1] : SSet.{u}) K ≫ L = p := by
    apply (cancel_mono q).1
    rw [Category.assoc, hLq]
    exact sliceOverUncurry_fixed F
  refine ⟨sliceOverCurry L hfixed, ?_⟩
  apply sliceOverUncurry_injective p
  rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
  exact hL

lemma reflects_colimit {K : SSet.{u}}
    {p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})} (c : JoinCocone p)
    (hc : IsColimitCone (F1B.kanPostcomposeCocone (fullSubcomplexOnVertices X P).ι c)) :
    IsColimitCone c := by
  intro n b hb
  let q := (fullSubcomplexOnVertices X P).ι
  let b' := b ≫ sliceUnderPostcomp p q
  have hb' : boundaryVertex n 0 ≫ b' =
      SSet.yonedaEquiv.symm (F1B.kanPostcomposeCocone q c) := by
    dsimp only [b']
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hc n b' hb'
  have hboundary : joinMap (𝟙 K) (boundary (n + 1)).ι ≫ sliceUnderUncurry F =
      sliceUnderUncurry b ≫ q := by
    rw [← sliceUnderUncurry_precomp, hF]
    exact sliceUnderUncurry_postcomp b q
  obtain ⟨L, hL, hLq⟩ := extension P _
    (DGNerve.joinMap_vertices_surjective _ _ (fun z ↦ ⟨z, rfl⟩)
      (DGNerve.boundary_vertices_surjective n)) (sliceUnderUncurry b) (sliceUnderUncurry F)
        hboundary
  have hfixed : joinInl K (Δ[n + 1] : SSet.{u}) ≫ L = p := by
    apply (cancel_mono q).1
    rw [Category.assoc, hLq]
    exact sliceUnderUncurry_fixed F
  refine ⟨sliceUnderCurry L hfixed, ?_⟩
  apply sliceUnderUncurry_injective p
  rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
  exact hL

end SerrePositivity.KST.LocalizingInvariants.FullSubcomplex
