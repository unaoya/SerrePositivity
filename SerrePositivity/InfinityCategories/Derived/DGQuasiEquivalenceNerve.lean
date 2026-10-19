module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorQuasiIsoFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGVertexIsoOfH0
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-! # 任意の dg 準同値の実 ∞ 圏同値

概要：全射性を要求しない dg 準同値は、native dg nerve の ∞ 圏同値を誘導する。
方針：実写像空間の充満忠実性と H⁰ の本質的全射から得た実頂点同型を合わせる。
規約：前三角性も不要。使われ方：β3 の平坦模型と β5 の dg 模型比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- dg 関手の H⁰ が本質的全射なら、実 nerve の対象も実同型まで覆う。 -/
lemma dgNerve_map_isEssentiallySurjective (F : DGFunctor A D E)
    (he : F.onHomotopy.EssSurj) : IsEssentiallySurjective (dgNerve.map F) := by
  let := he
  intro y
  obtain ⟨y, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  let Y := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) y)
  let X := F.onHomotopy.objPreimage Y
  let x := ForgetEnrichment.to (Complex A) X.as
  refine ⟨Simplex.vertex x, ?_⟩
  rw [dgFunctorNerve_vertex]
  exact ⟨dgVertexIsoOfH0 A E (F.onHomotopy.objObjPreimageIso Y)⟩

/-- 一般の dg 準同値の native nerve は ∞ 圏同値である。 -/
theorem dgNerve_map_isQCatEquivalence_of_quasiEquivalence (F : DGFunctor A D E)
    (h : QuasiEquivalence F) : IsQCatEquivalence (dgNerve.map F) :=
  (qCatEquivalenceOfFullyFaithfulEssentiallySurjective (dgNerve.map F)
    (dgNerve_map_isFullyFaithful_of_quasiIso F h.1)
    (dgNerve_map_isEssentiallySurjective F h.2)).isQCatEquivalence

/-- dg 準同値から明示的な ∞ 圏同値を選ぶ。 -/
def dgQuasiEquivalenceNerveEquivalence (F : DGFunctor A D E) (h : QuasiEquivalence F) :
    QCatEquivalence (dgNerve A D) (dgNerve A E) :=
  (dgNerve_map_isQCatEquivalence_of_quasiEquivalence F h).choose

end SerrePositivity.InfinityCategories
