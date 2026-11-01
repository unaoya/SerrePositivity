module
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyPrism
public import SerrePositivity.InfinityCategories.Derived.DGCoherentCompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStandardPinchedNaturality
public import SerrePositivity.InfinityCategories.Core.Roof.SliceOverEqualityTransport
/-!
概要：元の coherent 合成 prism の両入力に対する dg 関手自然性を公開する。
方針：標準 DK 係数と coherent 比較の自然性を、固定標的の slice へ移す。
規約：Small 仮定なしに全パラメーター・全時刻・端点輸送を保持する。
使われ方：D2 の閉前合成・閉後合成 prism を同じ coherent 構成のまま比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]

lemma dgPinchedCompositionTargetPoint_naturality (Q : DGFunctor A D E) (z : D) :
    (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex z) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj z)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Simplex.ext
  apply SimplexData.ext
  · rfl
  · exact zero_hom_heq _ _

lemma dgPinchedCompositionPrism_naturality (Q : DGFunctor A D E) (x y z : D)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex z) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj z)) :=
      dgPinchedCompositionTargetPoint_naturality A D E Q z) :
    dgPinchedCompositionPrism A D x y z ≫ sliceOverPostcomp _ (dgNerve.map Q) ≫
      (eqToIso (congrArg sliceOver hp)).hom =
      (Δ[1] ◁ (pinchedHomChainMap (Q.map x y) ⊗ₘ pinchedHomChainMap (Q.map y z))) ≫
        dgPinchedCompositionPrism A E (Q.obj x) (Q.obj y) (Q.obj z) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change ((eqToIso (congrArg sliceOver hp)).hom.app _
    ((sliceOverPostcomp _ (dgNerve.map Q)).app _
      ((dgPinchedCompositionPrism A D x y z).app _ a))).val = _
  rw [roofSliceTransport_val hp]
  let σ := ((standardHomPinchedIso (R := A) x y).inv.app _ a.2.1).down
  let τ := ((standardHomPinchedIso (R := A) y z).inv.app _ a.2.2).down
  let σ' := ((standardHomPinchedIso (R := A) (Q.obj x) (Q.obj y)).inv.app _
    ((pinchedHomChainMap (Q.map x y)).app _ a.2.1)).down
  let τ' := ((standardHomPinchedIso (R := A) (Q.obj y) (Q.obj z)).inv.app _
    ((pinchedHomChainMap (Q.map y z)).app _ a.2.2)).down
  let t := (SSet.stdSimplex.objEquiv a.1).toOrderHom
  change ((dgCoherentTargetSliceMap A D z).app _
      (coherentCompositionSliceSimplex (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
        (Z := ForgetEnrichment.of (Complex A) z) σ τ t)).val ≫ dgNerve.map Q =
    ((dgCoherentTargetSliceMap A E (Q.obj z)).app _
      (coherentCompositionSliceSimplex (C := ClosedCategory A E)
        (X := ForgetEnrichment.of (Complex A) (Q.obj x))
        (Y := ForgetEnrichment.of (Complex A) (Q.obj y))
        (Z := ForgetEnrichment.of (Complex A) (Q.obj z)) σ' τ' t)).val
  rw [dgCoherentTargetSliceMap_val, dgCoherentTargetSliceMap_val]
  simp only [coherentCompositionSliceSimplex, Category.assoc, SSet.yonedaEquiv_symm_comp]
  have hσ : σ' = dgStandardSimplexMap (Q.map x y) σ :=
    dgStandardPinchedIso_inv_naturality (Q.map x y) a.2.1
  have hτ : τ' = dgStandardSimplexMap (Q.map y z) τ :=
    dgStandardPinchedIso_inv_naturality (Q.map y z) a.2.2
  rw [hσ, hτ]
  apply congrArg (fun s : Simplex A E (n + 1) => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A E)).symm s)
  exact (dgCoherentSimplex_naturality Q _).trans
    (congrArg (fun s => coherentSimplex s) (dgCoherentCompositionSimplex_naturality Q σ τ t))

lemma dgPinchedCompositionFamilyPrism_naturality (Q : DGFunctor A D E)
    {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex z) ≫ dgNerve.map Q =
      (SSet.yonedaEquiv (X := dgNerve A E)).symm (Simplex.vertex (Q.obj z)) :=
      dgPinchedCompositionTargetPoint_naturality A D E Q z) :
    dgPinchedCompositionFamilyPrism A D f g ≫ sliceOverPostcomp _ (dgNerve.map Q) ≫
      (eqToIso (congrArg sliceOver hp)).hom =
    dgPinchedCompositionFamilyPrism A E
      (f ≫ pinchedHomChainMap (Q.map x y)) (g ≫ pinchedHomChainMap (Q.map y z)) := by
  unfold dgPinchedCompositionFamilyPrism
  rw [Category.assoc, dgPinchedCompositionPrism_naturality A D E Q x y z hp]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, CartesianMonoidalCategory.lift_map]
end SerrePositivity.InfinityCategories
