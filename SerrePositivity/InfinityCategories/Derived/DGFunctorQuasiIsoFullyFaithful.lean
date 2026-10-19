module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapQuasiIso
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 一般 Hom 準同型な dg 関手の実充満忠実性

概要：全射性を要求しない Hom 準同型から dg nerve の実充満忠実性を得る。
方針：Hom 鎖写像の一般準同型不変性を、端点の厳密な輸送同型と合成する。
規約：対象の全射性も不要。使われ方：β3 の局所 Hom と β5 の準同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 一つの Hom 上の一般準同型は、その実 pinched 写像空間上の同値を与える。 -/
lemma dgFunctor_pinchedHomMap_quasiIso_equivalence (F : DGFunctor A D E) (x y : D)
    (hq : QuasiIso (F.map x y)) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y)) := by
  let := hq
  let e := pinchedEndpointIso (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y)
  have he : pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y) =
      pinchedHomChainMap (F.map x y) ≫ e.inv := by
    rw [← dgFunctor_pinchedHomMap_eq]
    change _ = (_ ≫ e.hom) ≫ e.inv
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [he]
  exact (pinchedHomChainMap_quasiIso_equivalence (F.map x y)).comp
    (qCatEquivalenceOfIso e.symm).isQCatEquivalence.isSimplicialHomotopyEquivalence

/-- 全射性を仮定しない Hom 準同型な dg 関手の native nerve は実充満忠実。 -/
theorem dgNerve_map_isFullyFaithful_of_quasiIso (F : DGFunctor A D E)
    (hq : HomQuasiIso F) : IsFullyFaithful (dgNerve.map F) := by
  intro x y
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  exact dgFunctor_pinchedHomMap_quasiIso_equivalence F x y (hq x y)

end SerrePositivity.InfinityCategories
