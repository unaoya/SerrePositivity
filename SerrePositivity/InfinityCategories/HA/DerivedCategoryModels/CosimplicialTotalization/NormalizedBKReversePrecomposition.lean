module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomSourceNaturality
/-!
概要：指定Moore反転のend移送は元の零延長した反転鎖射の前合成そのもの。
方針：同じend–Hom同型の重みに関する自然性で両同型を打ち消す。
規約：IS-W2 B02の証明分割。指定射をホモトピー類だけで照合しない。
使われ方：HA 1.2.4、元の反転BK錐代表とA12の指定射の厳密な一致。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite AlgebraicTopology CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]
/-- 同じ指定反転の順射は元の反転鎖射による前合成に厳密に等しい。 -/
theorem normalizedBKReverseHomotopyEquiv_hom (X : CosimplicialObject (Complex A)) :
    (normalizedBKReverseHomotopyEquiv X).hom =
      intervalHomPrePost A
        (HomologicalComplex.extendMap
          (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
          ComplexShape.embeddingDownNat)
        (𝟙 ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
          (doubleOppositeDiagram X))) := by
  change (weightEndHomIso A _ (doubleOppositeDiagram X)).inv ≫
      ((linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
        (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight)).op ≫
      (weightEndHomIso A _ (doubleOppositeDiagram X)).hom) = _
  rw [weightEndHomIso_source_naturality, Iso.inv_hom_id_assoc]
/-- 指定反転の閉零次元での値は、同じ反転鎖射を前合成した実複体射。 -/
theorem normalizedBKReverseHomotopyEquiv_ofHom (X : CosimplicialObject (Complex A))
    (f : normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat ⟶
      (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
        (doubleOppositeDiagram X)) :
    (normalizedBKReverseHomotopyEquiv X).hom.f 0 (Cochain.ofHom f) =
      Cochain.ofHom (HomologicalComplex.extendMap
        (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat ≫ f) := by
  rw [normalizedBKReverseHomotopyEquiv_hom]
  apply Cochain.ext₀
  intro i
  change ((Cochain.ofHom (HomologicalComplex.extendMap
      (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
      ComplexShape.embeddingDownNat)).comp
    ((Cochain.ofHom f).comp (Cochain.ofHom (𝟙 _)) (add_zero 0)) (zero_add 0)).v i i
      (add_zero i) = _
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.comp_id, HomologicalComplex.comp_f]
/-- 元の恒等射から作った指定錐代表は、反転後も同じ実代表へ移る。 -/
theorem normalizedBKReverseHomotopyEquiv_coneRepresentative (X : CosimplicialObject (Complex A)) :
    (normalizedBKReverseHomotopyEquiv
      ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)).hom.f 0
        (Cochain.ofHom (normalizedBousfieldKanConeRepresentative X)) =
      Cochain.ofHom (reflectedBousfieldKanConeRepresentative X) := by
  rw [normalizedBKReverseHomotopyEquiv_ofHom]
  rfl
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
