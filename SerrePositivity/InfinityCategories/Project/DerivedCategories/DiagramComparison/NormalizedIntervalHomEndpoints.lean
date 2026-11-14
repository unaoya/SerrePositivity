module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalEndpointValues
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramTensorUnit
/-!
概要：指定正規化区間による図式ホモトピー評価の二端を同定する。
方針：同じ内部Homの端点等式とテンソル–Homの単位則を使う。
規約：A06の端点等式。図式の元の射f,gとの厳密等式を返す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 同じホモトピー区間評価の内部Homにおける両端。 -/
theorem homotopyIntervalCochainMap_endpoints (A : Type u) [CommRing A]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
    {R S : CochainComplex C ℤ} (f g : R ⟶ S) (h : Homotopy f g) :
    normalizedIntervalEndpointChain A 0 ≫ homotopyIntervalCochainMap A f g h =
      unitFromCycle (linearHomComplex A R S) ⟨Cochain.ofHom f, δ_ofHom f⟩ ∧
    normalizedIntervalEndpointChain A 1 ≫ homotopyIntervalCochainMap A f g h =
      unitFromCycle (linearHomComplex A R S) ⟨Cochain.ofHom g, δ_ofHom g⟩ := by
  exact normalizedIntervalCochainMapOfBoundary_endpoints A (linearHomComplex A R S)
    (Cochain.ofHom f) (Cochain.ofHom g) (δ_ofHom f) (δ_ofHom g)
    (-Cochain.ofHomotopy h) (by
      rw [map_neg]
      change -δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom g - Cochain.ofHom f
      rw [δ_ofHomotopy, neg_sub])
variable {A : Type (max u v)} [CommRing A] {J : Type v} [SmallCategory J]
local notation "E" => functorToComplexOfFunctors J (ModuleCat A) (ComplexShape.up ℤ)
/-- 指定パラメータ同型は区間端点を同じ定数図式の端点へ送る。 -/
theorem normalizedIntervalEndpoint_parameter (ε : Fin 2) :
    normalizedIntervalEndpoint A J ε ≫ (freeStandardSimplexParameterIso A J).hom.app ⦋1⦌ =
      (Functor.const J).map (normalizedIntervalEndpointChain A ε) := by
  apply NatTrans.ext
  funext j
  change normalizedIntervalEndpointChain A ε ≫ 𝟙 _ = _
  exact Category.comp_id _
/-- 同じ図式ホモトピーの指定区間評価は元のf,gを両端に持つ。 -/
theorem normalizedIntervalHom_endpoints {R S : J ⥤ Complex A} (f g : R ⟶ S)
    (h : Homotopy ((E).map f) ((E).map g)) :
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint A J 0) ≫
      normalizedIntervalHom f g h = f ∧
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ normalizedIntervalEndpoint A J 1) ≫
      normalizedIntervalHom f g h = g := by
  let T := (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
    (SSet.stdSimplex.obj ⦋1⦌)
  let t := (diagramTensorLinearHomEquiv R S T).symm
    (homotopyIntervalCochainMap A ((E).map f) ((E).map g) h)
  have ht0 : (R ◁ (Functor.const J).map (normalizedIntervalEndpointChain A 0)) ≫ t =
      (ρ_ R).hom ≫ f := by
    apply (diagramTensorLinearHomEquiv R S (𝟙_ (Complex A))).injective
    rw [diagramTensorLinearHomEquiv_precomp, diagramTensorLinearHomEquiv_unit]
    dsimp only [t]
    erw [Equiv.apply_symm_apply]
    exact (homotopyIntervalCochainMap_endpoints A ((E).map f) ((E).map g) h).1
  have ht1 : (R ◁ (Functor.const J).map (normalizedIntervalEndpointChain A 1)) ≫ t =
      (ρ_ R).hom ≫ g := by
    apply (diagramTensorLinearHomEquiv R S (𝟙_ (Complex A))).injective
    rw [diagramTensorLinearHomEquiv_precomp, diagramTensorLinearHomEquiv_unit]
    dsimp only [t]
    erw [Equiv.apply_symm_apply]
    exact (homotopyIntervalCochainMap_endpoints A ((E).map f) ((E).map g) h).2
  have he (ε : Fin 2) : (R ◁ normalizedIntervalEndpoint A J ε) ≫
      normalizedIntervalHom f g h =
        (R ◁ (Functor.const J).map (normalizedIntervalEndpointChain A ε)) ≫ t := by
    dsimp only [normalizedIntervalHom]
    rw [← Category.assoc, ← whiskerLeft_comp, normalizedIntervalEndpoint_parameter]
  constructor
  · rw [id_tensorHom, he, ht0, Iso.inv_hom_id_assoc]
  · rw [id_tensorHom, he, ht1, Iso.inv_hom_id_assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
