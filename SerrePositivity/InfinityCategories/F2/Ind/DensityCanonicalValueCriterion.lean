module

public import SerrePositivity.InfinityCategories.F2.Ind.CanonicalIntervalYonedaValue

/-!
概要：元の comma の値写像の同値性を、同じ Tw 恒等点からの大域密度輸送へ帰着する。
方針：証明済みの二つの Yoneda 評価同値と、全 fiber 上の区間作用の同型を使う。
規約：帰着は同じ指定射の同値性の同値であり、輸送の同値性自身は別途示す。
使われ方：元の恒等点復元射と同じ区間族の輸送比較への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 元の comma の実際の値写像は、同じ Tw 恒等点からの大域密度輸送が同値のとき、かつそのときに同値。 -/
lemma presheafElementsYonedaSliceValue_iff_canonicalTransport :
    IsQCatEquivalence (presheafElementsYonedaSliceValue F x) ↔
      IsQCatEquivalence (presheafDensityCanonicalTransportValue F x) := by
  have hi := intervalYonedaEvaluation_isQCatEquivalence F x
  have hc := canonicalIntervalYonedaEvaluation_isQCatEquivalence F x
  constructor
  · intro h
    have h' := h.ofFunctorIso (presheafDensityFiberYonedaValueIso F x)
    have hm := hi.cancel_right h'
    exact (hm.comp hc).ofFunctorIso (presheafDensityCanonicalFiberTransportIso F x)
  · intro h
    have h' := h.ofFunctorIso (presheafDensityCanonicalFiberTransportIso F x).symm
    have hm := hc.cancel_right h'
    exact (hm.comp hi).ofFunctorIso (presheafDensityFiberYonedaValueIso F x).symm

end SerrePositivity.InfinityCategories.F2.Ind
