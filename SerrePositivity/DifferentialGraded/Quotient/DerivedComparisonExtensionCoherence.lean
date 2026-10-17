module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonAdjointUnit
public import SerrePositivity.DifferentialGraded.Verdier.FiniteCellHomotopy

/-! # 導来延長とホモトピー有限 cell 上の underived 延長の自然同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

private lemma comparison_naturality
    {C₀ C₁ T₀ T₁ : Type*} [Category* C₀] [Category* C₁] [Category* T₀] [Category* T₁]
    (Q : C₀ ⥤ T₀) (P : C₁ ⥤ T₁) (G : C₀ ⥤ C₁) (R₀ : C₁ ⥤ C₀)
    (L : T₀ ⥤ T₁) (R : T₁ ⥤ T₀) (a : G ⊣ R₀) (b : L ⊣ R)
    (c : ∀ N, R.obj (P.obj N) ≅ Q.obj (R₀.obj N))
    (δ : ∀ M, L.obj (Q.obj M) ⟶ P.obj (G.obj M))
    (hδ : ∀ M N (s : G.obj M ⟶ N),
      b.homEquiv _ _ (δ M ≫ P.map s) = Q.map (a.homEquiv _ _ s) ≫ (c N).inv)
    {M N : C₀} (f : M ⟶ N) :
    L.map (Q.map f) ≫ δ N = δ M ≫ P.map (G.map f) := by
  have hi : b.homEquiv _ _ (δ N) = Q.map (a.homEquiv _ _ (𝟙 (G.obj N))) ≫
      (c (G.obj N)).inv := by
    simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hδ N (G.obj N) (𝟙 _)
  apply (b.homEquiv _ _).injective
  rw [b.homEquiv_naturality_left, hi, hδ]
  have hn := a.homEquiv_naturality_left f (𝟙 (G.obj N))
  simp only [Category.comp_id] at hn
  rw [hn, CategoryTheory.Functor.map_comp, Category.assoc]

lemma derivedExtensionUnderivedMap_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgDerivedExtension A D E F).map ((moduleToDerived A D).map f) ≫
        derivedExtensionUnderivedMap A D E F N =
      derivedExtensionUnderivedMap A D E F M ≫
        (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) := by
  exact comparison_naturality (moduleToDerived A D) (moduleToDerived A E)
    (dgModuleExtension A D E F).onClosed (dgModuleRestriction A D E F.op).onClosed
    (dgDerivedExtension A D E F) (dgDerivedRestriction A D E F)
    (dgModuleEnrichedRestrictionAdjunction A D E F)
    (dgDerivedExtensionRestrictionAdjunction A D E F)
    (dgDerivedRestrictionComputation A D E F) (derivedExtensionUnderivedMap A D E F)
    (fun M N s => by
      rw [dgDerivedExtensionRestrictionAdjunction_homEquiv]
      exact derivedExtensionUnderivedMap_homEquiv A D E F M N s) f

def derivedExtensionUnderivedNatTrans :
    moduleToDerived A D ⋙ dgDerivedExtension A D E F ⟶
      (dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E where
  app M := derivedExtensionUnderivedMap A D E F M
  naturality _ _ f := derivedExtensionUnderivedMap_naturality A D E F f

def extensionHomotopyComputationNatIso :
    moduleToHomotopy A D ⋙ dgExtensionHomotopyToDerived A D E F ≅
      (dgModuleExtension A D E F).onClosed ⋙ moduleToDerived A E :=
  NatIso.ofComponents (dgExtensionHomotopyComputation A D E F)
    (fun f => dgExtensionHomotopyComputation_naturality A D E F f)

/-- 導来化からホモトピー圏上の延長への比較を、商関手の前置の充満性で降ろす。 -/
def homotopyDerivedExtensionComparison :
    moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F ⟶
      dgExtensionHomotopyToDerived A D E F :=
  ((whiskeringLeft _ _ _).obj (moduleToHomotopy A D)).preimage
    ((isoWhiskerRight (moduleToHomotopyDerivedIso A D) (dgDerivedExtension A D E F)).hom ≫
      derivedExtensionUnderivedNatTrans A D E F ≫
        (extensionHomotopyComputationNatIso A D E F).inv)

lemma homotopyDerivedExtensionComparison_app (M : ModuleCategory A D) :
    (homotopyDerivedExtensionComparison A D E F).app ((moduleToHomotopy A D).obj M) =
      (dgDerivedExtension A D E F).map ((moduleToHomotopyDerivedIso A D).hom.app M) ≫
        derivedExtensionUnderivedMap A D E F M ≫
          (dgExtensionHomotopyComputation A D E F M).inv := by
  exact congrArg (fun τ => τ.app M)
    (((whiskeringLeft _ _ _).obj (moduleToHomotopy A D)).map_preimage
      (X := moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F)
      (Y := dgExtensionHomotopyToDerived A D E F)
      ((isoWhiskerRight (moduleToHomotopyDerivedIso A D) (dgDerivedExtension A D E F)).hom ≫
        derivedExtensionUnderivedNatTrans A D E F ≫
          (extensionHomotopyComputationNatIso A D E F).inv))

lemma homotopyDerivedExtensionComparison_isIso {S : Set D}
    (X : HomotopyFiniteCellCategoryOver A D S) :
    IsIso ((homotopyDerivedExtensionComparison A D E F).app X.obj) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := X.property
  have hi : IsIso ((homotopyDerivedExtensionComparison A D E F).app
      ((moduleToHomotopy A D).obj M)) := by
    rw [homotopyDerivedExtensionComparison_app]
    let := derivedExtensionUnderivedMap_isIso A D E F M
      (moduleFiniteCellOver_homotopicallyProjective A D hM)
    infer_instance
  let := hi
  have hn := (homotopyDerivedExtensionComparison A D E F).naturality e.hom
  have hc : IsIso ((moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F).map e.hom ≫
      (homotopyDerivedExtensionComparison A D E F).app X.obj) := by
    rw [hn]
    infer_instance
  let := hc
  exact IsIso.of_isIso_comp_left
    ((moduleHomotopyToDerivedClosed A D ⋙ dgDerivedExtension A D E F).map e.hom) _

/-- 有限 cell 部分圏上での、二つの延長計算の実際の自然同型。 -/
def finiteCellHomotopyDerivedExtensionIso (S : Set D) :
    (homotopyFiniteCellOver A D S).ι ⋙ moduleHomotopyToDerivedClosed A D ⋙
        dgDerivedExtension A D E F ≅
      (homotopyFiniteCellOver A D S).ι ⋙ dgExtensionHomotopyToDerived A D E F := by
  let τ := whiskerLeft (homotopyFiniteCellOver A D S).ι
    (homotopyDerivedExtensionComparison A D E F)
  let : ∀ X, IsIso (τ.app X) := fun X => homotopyDerivedExtensionComparison_isIso A D E F X
  let := NatIso.isIso_of_isIso_app τ
  exact asIso τ

end SerrePositivity.DifferentialGraded.DGQuotient
