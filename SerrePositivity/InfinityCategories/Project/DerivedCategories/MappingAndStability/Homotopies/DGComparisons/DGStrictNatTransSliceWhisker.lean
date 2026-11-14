module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGStrictNatTransHomotopyWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGStrictNatTransPinchedSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofSliceTransport

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (B C D E : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A B] [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C D}

/-- 固定標的の等式輸送込みで、後合成と全 slice prism は厳密に可換。 -/
lemma dgStrictNatTransPostcomp_pinchedSlice (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x y : C)
    (hp : (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (G.obj y)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q = (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Q.obj (G.obj y)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A C D η x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q) ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A C E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q) x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom.app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)).app _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSliceSimplex A C D η x y s.1
        (SSet.stdSimplex.objEquiv s.2).toOrderHom))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.roofSliceTransport_val hp]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (η.simplex s.1.val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase
      (SSet.stdSimplex.objEquiv s.2).toOrderHom))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q = _
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1) => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_simplex η Q s.1.val
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)).symm

/-- 始域の Hom 鎖写像による全係数の引き戻しと、前合成後の prism は一致。 -/
lemma dgStrictNatTransPrecomp_pinchedSlice (P : _root_.SerrePositivity.DifferentialGraded.DGFunctor A B C)
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (x y : B) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (P.map x y) ▷ (Δ[1] : SSet.{max u v})) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A C D η (P.obj x) (P.obj y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPinchedSlice A B D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp P η) x y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
    (η.simplex (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (P.map x y)).app _ s.1).val)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)) = _
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorPinchedChainMap_val A P s.1
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1) => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm t)
      ((congrArg (fun t => η.simplex t
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)) h).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp_simplex P η s.1.val
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedPrismPhase (SSet.stdSimplex.objEquiv s.2).toOrderHom)).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
