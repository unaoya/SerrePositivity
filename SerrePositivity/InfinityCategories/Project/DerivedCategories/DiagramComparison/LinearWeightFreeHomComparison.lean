module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightFreeDiagramEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CopowerNormalizedFreeHom
/-!
概要：元の線形重みHom同値を同じ図式自由鎖随伴へ全単体で照合する。
方針：指定比較の評価公式と点ごとの正規化Hom両立を生成元で適用する。
規約：IS-W2 B02の同じ係数移送の証明分割。元のA12の比較の射を保つ。
使われ方：HA 1.2.4、元のBK錐代表とA09の自由鎖Hom比較への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
/-- 元の線形重みHom同値は指定自由重み比較の後で同じ自由鎖随伴に一致する。 -/
theorem normalizedLinearWeightHomEquiv_freeDiagram (W : J ⥤ SSet.{0})
    (H : CochainComplex (J ⥤ ModuleCat A) ℤ)
    (f : (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ⟶ H) :
    (flipFunctor SimplexCategoryᵒᵖ J (Type u)).map
        (normalizedLinearWeightHomEquiv A W.flip H
          ((normalizedLinearWeightDiagramIso A W).hom ≫ f)) ≫
      Functor.whiskerRight ((pointwiseTruncationGammaIso J (ModuleCat A)).hom.app H)
        ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat A) (Type u)).obj
          (forget (ModuleCat A))) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv (W ⋙ SSet.uliftFunctor.{u,0})
      (complexOfFunctorsToFunctorToComplex.obj H)
      ((functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
          (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ≫
        complexOfFunctorsToFunctorToComplex.map f) := by
  let V := linearizedSimplicialWeight A W.flip
  let T := (Functor.whiskeringRight J (ChainComplex (ModuleCat A) ℕ)
    (CochainComplex (ModuleCat A) ℤ)).obj (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))
  let b := (pointwiseMooreFunctor J (ModuleCat A)).map
    (linearizedSimplicialWeightFreeIso A W.flip).hom
  let f' := (functorComplexExchangeUnitIso J (ModuleCat A) (.up ℤ)).hom.app
    (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) ≫
      complexOfFunctorsToFunctorToComplex.map f
  have hm := pointwiseNormalizedWeightHomEquiv J (ModuleCat A) V H
    ((normalizedLinearWeightDiagramIso A W).hom ≫ f)
  have hf : T.map ((pointwiseMooreIso J (ModuleCat A)).inv.app V) ≫
      (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).inv.app
        ((normalizedMooreComplex _).obj V) ≫
      complexOfFunctorsToFunctorToComplex.map ((normalizedLinearWeightDiagramIso A W).hom ≫ f) =
      T.map b ≫ f' := by
    rw [Functor.map_comp]
    have h := congrArg (fun t => t ≫ complexOfFunctorsToFunctorToComplex.map f)
      (normalizedLinearWeightDiagramIso_hom_evaluation A W)
    simp only [Category.assoc] at h
    exact h
  rw [hf] at hm
  apply NatTrans.ext
  funext j
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  let x := Sigma.ι (fun _ : (W.obj j).obj n => ModuleCat.of A A) s.down (1 : A)
  have h := congrArg (fun t => ((t.app j).app n) x) hm
  have h' := congrArg (fun t => (t.app n) s)
    (copowerNormalizedHomEquiv_free A (W.obj j)
      ((complexOfFunctorsToFunctorToComplex.obj H).obj j) (f'.app j))
  refine h.trans ?_
  simp only [normalizedWeightHomEquiv_asAdjunction, freeNegativeChainsDiagramAdjunction,
    Adjunction.homEquiv_apply, Adjunction.comp_unit_app, Adjunction.whiskerRight_unit_app_app,
    Functor.map_comp, NatTrans.comp_app, Functor.whiskeringRight_obj_map,
    Functor.whiskerRight_app] at h' ⊢
  simp only [V, T, b, x, f', copowerUnitDiagramHomEquiv, copowerUnitDiagramHomTo,
    copowerUnitHomEquiv, pointwiseMooreFunctor, Functor.comp_map,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.map_comp] at h' ⊢
  exact h'
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
