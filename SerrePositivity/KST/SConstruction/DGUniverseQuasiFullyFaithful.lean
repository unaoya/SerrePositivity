module
public import SerrePositivity.InfinityCategories.Derived.DGUniverseNerveFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGFunctorQuasiIsoFullyFaithful

/-! # Hom 準同型な実 dg 関手の共通宇宙での充満忠実性
概要：異なる対象宇宙の dg 関手でも、Hom 準同型性は実 nerve の充満忠実性を与える。
方針：元の関手を同じ宇宙に持ち上げ、既存の実写像空間の判定を輸送する。
規約：対象上の全射性を仮定しない。使われ方：実 Perf 右軸包含。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {D : Type w} [DGCategory R D]

/-- 全 Hom 準同型な元の dg 関手は、共通宇宙の実 nerve 上で充満忠実。 -/
lemma dgNerveUniverseMap_fullyFaithful_of_homQuasiIso (F : DGFunctor R C D)
    (h : HomQuasiIso F) : IsFullyFaithful (dgNerveUniverseMap F) := by
  have hf : IsFullyFaithful (dgNerve.map (dgUniverseLiftFunctor.{u, v, w, w, v} F)) :=
    dgNerve_map_isFullyFaithful_of_quasiIso _ (fun x y => h x.label.down y.label.down)
  rw [dgNerveUniverseMap_factor]
  have hc := (qCatEquivalenceOfIso
    (dgNerveUniverseLiftIso.{u, v, w} R C)).isQCatEquivalence.isFullyFaithful
  have hd := (qCatEquivalenceOfIso
    (dgNerveUniverseLiftIso.{u, w, v} R D).symm).isQCatEquivalence.isFullyFaithful
  exact hc.comp (hf.comp hd)

end SerrePositivity.KST.SConstruction
