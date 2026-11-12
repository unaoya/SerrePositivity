module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaConeCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeZeroAction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaPrecomposeEvaluation

/-! # Yoneda cone 元の閉細分と元の Hom の二座標

概要：実 cone 元の Yoneda 像を元の閉射で前合成すると、二座標とも同じ閉射で前合成される。
方針：Yoneda 評価と閉前合成の整合性、加群 cone の作用、元の二座標の回収を合成する。
規約：全整数次数。使われ方：追加分母後の原始元を Q・A の二未知式へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉細分後の評価の第一座標は、元の第一座標の同じ閉射による前合成。 -/
lemma dgYonedaConePrecompose_fst (x q : D) {y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (g : y ⟶ z)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (n : ℤ)
    (a : (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).X n) :
    (mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))).val.v
      n (n + 1) rfl
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom.f n
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a) s)) =
      _root_.SerrePositivity.DifferentialGraded.compose A ((mappingCone.fst
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).val.v n (n + 1) rfl a)
          (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add (n + 1)) := by
  let M := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g)
  let b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a
  let c := (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A x M).hom.f n b
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose_evaluation A D x q M n b s
  have h₁ := congrArg ((mappingCone.fst
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))).val.v n (n + 1) rfl) he
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroAction_fst A D ((dgYoneda A D).onClosed.map g)
    x q (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val n c
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableZeroAction A D x q y (n + 1)
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val
    ((mappingCone.fst ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D x).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))).val.v
      n (n + 1) rfl c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => _root_.SerrePositivity.DifferentialGraded.compose A t (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso_fst A D x g n a))))

/-- 閉細分後の評価の第二座標は、元の第二座標の同じ閉射による前合成。 -/
lemma dgYonedaConePrecompose_snd (x q : D) {y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (g : y ⟶ z)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (n : ℤ)
    (a : (mappingCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).X n) :
    (mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))).v
      n n (add_zero n)
      ((dgYonedaIso A q (ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g))).hom.f n
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D n
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a) s)) =
      _root_.SerrePositivity.DifferentialGraded.compose A ((mappingCone.snd
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (closedHomEquiv A D y z g))).v n n (add_zero n) a)
          (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add n) := by
  let M := ForgetEnrichment.to (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaClosedCone A D g)
  let b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso A D x g).hom.f n a
  let c := (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A x M).hom.f n b
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose_evaluation A D x q M n b s
  have h₁ := congrArg ((mappingCone.snd
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D q).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))).v n n (add_zero n)) he
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroAction_snd A D ((dgYoneda A D).onClosed.map g)
    x q (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val n c
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableZeroAction A D x q z n (closedHomEquiv A D _ _ s).val
    ((mappingCone.snd ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D x).map ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map g))).v
      n n (add_zero n) c)
  exact h₁.trans (h₂.trans (h₃.trans (congrArg
    (fun t => _root_.SerrePositivity.DifferentialGraded.compose A t (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add n))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaPostcompositionConeIso_snd A D x g n a))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
