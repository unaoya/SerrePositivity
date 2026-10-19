module
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransHomotopyWhisker
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransPinchedSlice
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Derived.RoofSliceTransport

/-! # 固定標的 slice prism の前後合成

概要：厳密自然変換の全係数 prism と dg 関手による前後合成を比較する。
方針：固定標的の等式輸送を外し、全二相単体の比較へ戻す。
規約：面・退化と全時刻を保持。使われ方：元・商の実屋根の輸送の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (B C D E : Type v)
variable [DGCategory A B] [DGCategory A C] [DGCategory A D] [DGCategory A E]
variable {F G : DGFunctor A C D}

/-- 固定標的の等式輸送込みで、後合成と全 slice prism は厳密に可換。 -/
lemma dgStrictNatTransPostcomp_pinchedSlice (η : StrictNatTrans F G)
    (Q : DGFunctor A D E) (x y : C)
    (hp : (SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex (G.obj y)) ≫
      dgNerve.map Q = (SSet.yonedaEquiv (X := dgNerve A E)).symm
        (Simplex.vertex (Q.obj (G.obj y)))) :
    dgStrictNatTransPinchedSlice A C D η x y ≫
      sliceOverPostcomp _ (dgNerve.map Q) ≫ (eqToIso (congrArg sliceOver hp)).hom =
      dgStrictNatTransPinchedSlice A C E (dgStrictNatTransPostcomp η Q) x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToIso (congrArg sliceOver hp)).hom.app _
    ((sliceOverPostcomp _ (dgNerve.map Q)).app _
      (dgStrictNatTransPinchedSliceSimplex A C D η x y s.1
        (SSet.stdSimplex.objEquiv s.2).toOrderHom))).val = _
  rw [roofSliceTransport_val hp]
  change ((joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    (η.simplex s.1.val (pinchedPrismPhase
      (SSet.stdSimplex.objEquiv s.2).toOrderHom))) ≫ dgNerve.map Q = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun t : Simplex A E (n + 1) => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A E)).symm t)
      (dgStrictNatTransPostcomp_simplex η Q s.1.val
        (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)).symm

/-- 始域の Hom 鎖写像による全係数の引き戻しと、前合成後の prism は一致。 -/
lemma dgStrictNatTransPrecomp_pinchedSlice (P : DGFunctor A B C)
    (η : StrictNatTrans F G) (x y : B) :
    (pinchedHomChainMap (P.map x y) ▷ (Δ[1] : SSet.{max u v})) ≫
      dgStrictNatTransPinchedSlice A C D η (P.obj x) (P.obj y) =
      dgStrictNatTransPinchedSlice A B D (dgStrictNatTransPrecomp P η) x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    (η.simplex (((pinchedHomChainMap (P.map x y)).app _ s.1).val)
      (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)) = _
  have h := dgFunctorPinchedChainMap_val A P s.1
  exact congrArg (fun t : Simplex A D (n + 1) => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A D)).symm t)
      ((congrArg (fun t => η.simplex t
        (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)) h).trans
          (dgStrictNatTransPrecomp_simplex P η s.1.val
            (pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)).symm)

end SerrePositivity.InfinityCategories
