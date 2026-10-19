module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSourceFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceSourceIdentity

/-!
概要：錐全体上の明示的な豊穣 Hom の族は、頂点で標準の Hom 比較を与える。
方針：錐の頂点での標準切断を恒等射と同定し、coslice の前合成の単位計算を適用する。
規約：局所 Kan 性・錐の極限性・頂点評価の逆の選択を用いない。
使われ方：HTT 4.2.4.1 の coend 余錐の普遍性の頂点条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {K : SSet.{max u v}} {p : K ⟶ SimplicialNerve C}

/-- 頂点を正規化した錐全体の標準切断の頂点制限も、恒等射の coslice 点になる。 -/
lemma coherentConeSourceSectionAt_apex (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) :
    joinInl (Δ[0] : SSet.{max u v}) K ≫ coherentConeSourceSectionAt c z hz =
      cosliceIdentityPoint (coherentNerveVertex z) := by
  have ht {a b : (SimplicialNerve C) _⦋0⦌} (h : a = b) :
      cosliceIdentityPoint a ≫ eqToHom (congrArg
        (fun w ↦ sliceUnder (SSet.yonedaEquiv.symm w)) h) = cosliceIdentityPoint b := by
    cases h
    exact Category.comp_id _
  rw [coherentConeSourceSectionAt, ← Category.assoc, coneIdentityCosliceSection_apex, ht hz]

/-- 明示的な錐全体の Hom の族の頂点評価は、標準の coslice fiber 比較そのもの。 -/
lemma coherentConeSourceFamily_evaluation (c : JoinCone p) (z : C)
    (hz : c.vertex = coherentNerveVertex z) (x : C) :
    coherentConeSourceFamily c z hz x ≫ coherentConeApexEvaluation c z hz x =
      coherentCosliceFiberComparison x z := by
  apply vertexFiber_hom_ext
    (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
    (coherentNerveVertex z)
  rw [Category.assoc, coherentConeApexEvaluation_ι,
    relativeFunctorUncurry_at_vertex, coherentConeSourceFamily_uncurry,
    ← Category.assoc, lift_whiskerRight, SSet.const_comp]
  have hv : (coherentConeSourceSectionAt c z hz).app (Opposite.op ⦋0⦌)
      (joinApexVertex K) =
      SSet.yonedaEquiv (cosliceIdentityPoint (coherentNerveVertex z)) := by
    have h := congrArg (fun f ↦ SSet.yonedaEquiv f)
      (coherentConeSourceSectionAt_apex c z hz)
    have hj : SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{max u v}) K) =
        joinApexVertex K := by
      change (joinInl (Δ[0] : SSet.{max u v}) K).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (𝟙 Δ[0])) = _
      congr 1
      apply stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
    simpa only [SSet.yonedaEquiv_comp, hj] using h
  rw [hv, coherentCosliceSourcePrecomposition_identity]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
