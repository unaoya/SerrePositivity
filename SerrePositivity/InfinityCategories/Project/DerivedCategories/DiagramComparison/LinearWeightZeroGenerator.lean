module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorCoefficientGeneratorValues
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreInverseInclusion
public import SerrePositivity.HomologicalAlgebra.MapExtendComponents

/-!
概要：指定線形重み比較の逆射は、第0項の同じ自由生成元を指定余積生成元へ戻す。
方針：零延長・点ごとのMoore比較・係数同型の第0項の単位則を合成する。
規約：IS-W2 C01の既存構成の係数移送則。生成元を選び直さない。
使われ方：HA 1.2.4、Tot錐の標準脚の零次評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open scoped Simplicial
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]

/-- 同じ零次の自由生成元は、指定線形重み比較の逆射と包含で元の余積生成元に戻る。 -/
theorem normalizedLinearWeightDiagramIso_inv_zero_generator (W : J ⥤ SSet.{0})
    (j : J) (s : (W.obj j) _⦋0⦌) :
    let V := linearizedSimplicialWeight A W.flip
    let N := (normalizedMooreComplex _).obj V
    let e := N.extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) rfl
    ((inclusionOfMooreComplexMap V).f 0).app j
      (e.hom.app j (((normalizedLinearWeightDiagramIso A W).inv.f 0).app j
        (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0 (ULift.up s)))) =
      CategoryTheory.Limits.Sigma.ι (fun _ : (W.obj j) _⦋0⦌ => ModuleCat.of A A) s (1 : A) := by
  let V := linearizedSimplicialWeight A W.flip
  let U := freeLinearizedSimplicialWeight A W.flip
  let F := (evaluation J (ModuleCat A)).obj j
  let c := (linearizedSimplicialWeightFreeIso A W.flip).inv
  have hc : (((normalizedMooreComplex _).map c).f 0).app j ≫
      ((inclusionOfMooreComplexMap V).f 0).app j =
    ((inclusionOfMooreComplexMap U).f 0).app j ≫ (c.app (Opposite.op ⦋0⦌)).app j := by
    exact congrArg (fun f => (f.f 0).app j)
      ((inclusionOfMooreComplex (J ⥤ ModuleCat A)).naturality c)
  have hm : (normalizedMooreMapIso F U).inv.f 0 ≫
      ((inclusionOfMooreComplexMap U).f 0).app j =
    (inclusionOfMooreComplexMap (U ⋙ F)).f 0 := by
    have h := congrArg (fun f => f.f 0) (normalizedMooreMapInv_inclusion F U)
    change (normalizedMooreMapIso F U).inv.f 0 ≫
      ((inclusionOfMooreComplexMap U).f 0).app j =
      (inclusionOfMooreComplexMap (U ⋙ F)).f 0 ≫ 𝟙 _ at h
    simpa only [Category.comp_id] using h
  have hma := congrArg (fun f => f ≫ (c.app (Opposite.op ⦋0⦌)).app j) hm
  simp only [Category.assoc] at hma
  let S := ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) ⋙ ModuleCat.free A
  have hp : (DoldKan.PInftyToNormalizedMooreComplex S).f 0 ≫
      (inclusionOfMooreComplexMap S).f 0 = 𝟙 _ := by
    have h := congrArg (fun f => f.f 0)
      (DoldKan.PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap S)
    simpa only [HomologicalComplex.comp_f, DoldKan.PInfty_f, DoldKan.P_f_0_eq] using h
  have hpa := congrArg (fun f => f ≫ (c.app (Opposite.op ⦋0⦌)).app j) hp
  simp only [Category.assoc, Category.id_comp] at hpa
  dsimp only [normalizedLinearWeightDiagramIso, Iso.trans_inv, normalizedLinearWeightFreeIso,
    freeLinearWeightDiagramIso, Functor.mapIso_inv, HomologicalComplex.comp_f,
    NatTrans.comp_app, ModuleCat.comp_apply]
  dsimp only [pointwiseMooreIso, pointwiseExtendIso, Iso.app, NatIso.ofComponents,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    ComplexShape.Embedding.extendFunctor]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
    (i := 0) (i' := (0 : ℤ)) (by rfl)]
  dsimp only [functorToComplexOfFunctors, functorComplexExchangeCounitIso,
    Iso.symm_inv, Iso.app, NatIso.ofComponents, Functor.whiskerRight_app,
    HomologicalComplex.eval, HomologicalComplex.Hom.isoOfComponents_hom_f,
    Iso.refl_hom, NatTrans.comp_app, ModuleCat.comp_apply]
  simp only [HomologicalComplex.comp_f]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
    (i := 0) (i' := (0 : ℤ)) (by rfl)]
  erw [mapExtendIso_inv_f ((evaluation J (ModuleCat A)).obj j)
    ComplexShape.embeddingDownNat _ (i := 0) (j := (0 : ℤ)) (by rfl)]
  simp only [← ModuleCat.comp_apply, Category.assoc,
    Iso.inv_hom_id_app_assoc, Category.comp_id]
  erw [Iso.inv_hom_id_assoc]
  dsimp only [evaluation]
  erw [Iso.inv_hom_id_app_assoc]
  erw [hc, hma]
  dsimp only [freeNegativeGenerator]
  erw [← ModuleCat.comp_apply, Iso.inv_hom_id_assoc]
  erw [← ModuleCat.comp_apply, hpa]
  change copowerUnitFreeInv A ((W.obj j) _⦋0⦌) (ModuleCat.freeMk (ULift.up s)) = _
  exact copowerUnitFreeInv_generator A _ (ULift.up s)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
