module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeRepresentativeNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.WeightEndHomTargetNaturality

/-!
概要：同じBK錐代表の頂点の前合成則と図式方向との両立を述べる。
方針：既存の任意次数の行合成則を閉零射へ特殊化し、行の指定同値で検出する。
規約：IS-W2 D01の既存構成の自然性・合成則。計算上限を上げない。
使われ方：HA 1.2.4、全図式射に沿う同じ指定Tot錐族の貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A]

/-- 同じ頂点の閉射を各Hom複体へ前合成する全図式射。 -/
def bousfieldKanHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    doubleOppositeDiagram ((homDiagramFunctor Q).obj X) ⟶
      doubleOppositeDiagram ((homDiagramFunctor P).obj X) where
  app j := homPrecompose f (X.obj ((opOpEquivalence SimplexCategory).functor.obj j))
  naturality i j a := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (Cochain.ofHom f).comp
        (z.comp (Cochain.ofHom (X.map ((opOpEquivalence SimplexCategory).functor.map a)))
          (add_zero q)) (zero_add q) =
      ((Cochain.ofHom f).comp z (zero_add q)).comp
        (Cochain.ofHom (X.map ((opOpEquivalence SimplexCategory).functor.map a))) (add_zero q)
    exact (Cochain.comp_assoc_of_third_is_zero_cochain _ _ _ _).symm

/-- 同じ頂点前合成の複体図式への像。 -/
def normalizedBKConeSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor Q).obj X)) ⟶
    (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X)) :=
  (functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).map
    (bousfieldKanHomSourceMap f X)

/-- 同じ頂点前合成を元の各Hom行で評価する。 -/
theorem normalizedBKConeSourceMap_f {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) (q : ℤ) :
    (normalizedBKConeSourceMap f X).f q =
      homDiagramDegreePrecompose X 0 q q (zero_add q) (Cochain.ofHom f) := rfl

/-- 指定BK錐代表は、頂点の同じ閉射の前合成を厳密に保つ。 -/
theorem normalizedBousfieldKanRepresentative_precompose {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (f : P ⟶ Q)
    (g : Q ⟶ (productTotalFunctor A).obj X) :
    normalizedBousfieldKanRepresentative Q X g ≫ normalizedBKConeSourceMap f X =
      normalizedBousfieldKanRepresentative P X (f ≫ g) := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, normalizedBousfieldKanRepresentative_cochain,
    normalizedBousfieldKanRepresentative_cochain]
  apply (extendedChainHomRowsLinearEquiv normalizedBousfieldKanWeight
    ((functorToComplexOfFunctors SimplexCategoryᵒᵖᵒᵖ (ModuleCat A) (.up ℤ)).obj
      (doubleOppositeDiagram ((homDiagramFunctor P).obj X))) A 0).injective
  funext n
  let z := (homToNormalizedBousfieldKan Q X).f 0 (Cochain.ofHom g)
  have hp := extendedChainHomRows_postcomp A normalizedBousfieldKanWeight
    (normalizedBKConeSourceMap f X) 0 z n
  change extendedChainHomRows _ _ 0
    ((Cochain.ofHom (𝟙 (normalizedBousfieldKanWeight.extend ComplexShape.embeddingDownNat))).comp
      (z.comp (Cochain.ofHom (normalizedBKConeSourceMap f X)) (add_zero 0)) (zero_add 0)) n = _ at hp
  rw [Cochain.id_comp] at hp
  change extendedChainHomRows _ _ 0
    (z.comp (Cochain.ofHom (normalizedBKConeSourceMap f X)) (add_zero 0)) n = _
  rw [hp, normalizedBKConeSourceMap_f]
  have h := homToNormalizedBousfieldKan_rows_comp_of_degree X 0 0 0 (by omega) n
    (Cochain.ofHom f) (Cochain.ofHom g)
  simp only [Int.mul_zero, Int.negOnePow_zero, one_smul, ← Cochain.ofHom_comp] at h
  exact h.symm

/-- 同じTot錐代表の図式方向と頂点方向の二つの自然性は一致する。 -/
theorem normalizedBousfieldKanConeRepresentative_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    normalizedBousfieldKanConeRepresentative X ≫
        normalizedBKConeTargetMap ((productTotalFunctor A).obj X) f =
      normalizedBousfieldKanConeRepresentative Y ≫
        normalizedBKConeSourceMap ((productTotalFunctor A).map f) Y := by
  have ht := normalizedBousfieldKanRepresentative_naturality
    ((productTotalFunctor A).obj X) f (𝟙 _)
  have hs := normalizedBousfieldKanRepresentative_precompose Y
    ((productTotalFunctor A).map f) (𝟙 _)
  simpa only [Category.id_comp, Category.comp_id, normalizedBousfieldKanConeRepresentative]
    using ht.trans hs.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
