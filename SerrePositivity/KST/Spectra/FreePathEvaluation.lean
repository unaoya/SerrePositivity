module

public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.KST.Spectra.PointedWeightedConeUnderlying

/-!
概要：自由 path を通常の二変数の評価射で読み、元の端点評価と照合する。
方針：自由基点の制限同型の自然性と単位での評価式を用いる。
規約：同じ実射を評価する。使われ方：写像 path トレースの通常の正方形への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open BraidedCategory
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.FreePathEvaluation

/-- 自由基点を除いた元の成分で評価する、通常の二変数の射。 -/
def evaluation (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    K ⊗ (PointedObject.basedHom (PointedObject.adjoin K) Y).right ⟶ Y.right :=
  uncurry (FreePointedHomRestriction.restrict K Y)

private lemma unit_evaluation (Y : PointedSimplicialSet.{u}) :
    evaluation (𝟙_ SSet.{u}) Y =
      snd (𝟙_ SSet.{u}) (PointedObject.basedHom (𝟙_ PointedSimplicialSet.{u}) Y).right ≫
        (unitIsoSelf (X := Y)).hom.right := by
  apply (cancel_epi ((𝟙_ SSet.{u}) ◁ (unitIsoSelf (X := Y)).inv.right)).mp
  change _ ≫ uncurry (FreePointedHomRestriction.restrict _ Y) = _
  rw [← uncurry_natural_left, PointedWeightedEnd.unit_inverse_restrict, uncurry_curry]
  change snd (𝟙_ SSet.{u}) Y.right =
    ((𝟙_ SSet.{u}) ◁ (unitIsoSelf (X := Y)).inv.right ≫
      snd (𝟙_ SSet.{u}) ((ihom (𝟙_ PointedSimplicialSet.{u})).obj Y).right) ≫
        (unitIsoSelf (X := Y)).hom.right
  rw [whiskerLeft_snd, Category.assoc, ← Under.comp_right, Iso.inv_hom_id,
    Under.id_right, Category.comp_id]

/-- 単位からの入力を固定した評価は、同じ自由基点の制限の単位評価。 -/
lemma evaluation_at_unit {K : SSet.{u}} (j : 𝟙_ SSet.{u} ⟶ K)
    (Y : PointedSimplicialSet.{u}) :
    (λ_ (PointedObject.basedHom (PointedObject.adjoin K) Y).right).inv ≫
        j ▷ (PointedObject.basedHom (PointedObject.adjoin K) Y).right ≫ evaluation K Y =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) Y ≫
        (unitIsoSelf (X := Y)).hom).right := by
  rw [evaluation, ← uncurry_pre_app, ← FreePointedHomRestriction.natural_pre,
    uncurry_natural_left]
  change _ ≫ ((𝟙_ SSet.{u}) ◁ _ ≫ evaluation (𝟙_ SSet.{u}) Y) = _
  rw [unit_evaluation]
  change (λ_ _).inv ≫ ((𝟙_ SSet.{u}) ◁
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map j) Y).right ≫
      snd (𝟙_ SSet.{u}) ((ihom (𝟙_ PointedSimplicialSet.{u})).obj Y).right ≫
        (unitIsoSelf (X := Y)).hom.right) = _
  rw [← Category.assoc ((𝟙_ SSet.{u}) ◁ _) _ _, whiskerLeft_snd,
    Category.assoc, ← Category.assoc (λ_ _).inv _ _, leftUnitor_inv_snd,
    Category.id_comp, Under.comp_right]

/-- 端点の自由基点追加は、元の区間の同じ定数頂点の追加そのもの。 -/
lemma endpoint_eq_map (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i = PointedObject.adjoinFunctor.map
      (PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫ stdSimplex.δ i) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint
  rw [Functor.map_comp]
  rfl

/-- 二つの変数を交換して、path を値とするパラメータ族の通常の正方形を得る。 -/
def square {A : SSet.{u}} {Y : PointedSimplicialSet.{u}}
    (F : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) : A ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right :=
  (β_ A (Δ[1] : SSet.{u})).hom ≫ uncurry
    (F ≫ FreePointedHomRestriction.restrict (Δ[1] : SSet.{u}) Y)

/-- 元の自由区間の端点で評価すると、同じ path 族の端点射になる。 -/
lemma square_face {A : SSet.{u}} {Y : PointedSimplicialSet.{u}}
    (F : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) (i : Fin 2) :
    (ρ_ A).inv ≫ A ◁ (PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫ stdSimplex.δ i) ≫
        square F = F ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y i).right := by
  let j := PointedSimplicialSet.deltaZeroUnitIso.{u}.inv ≫ stdSimplex.δ i
  change (ρ_ A).inv ≫ A ◁ j ≫ square F = _
  rw [square, uncurry_natural_left, braiding_naturality_right_assoc,
    braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (j ▷ A), ← whisker_exchange, Category.assoc,
    ← leftUnitor_inv_naturality_assoc]
  change F ≫ ((λ_ (PointedObject.basedHom
      (PointedObject.adjoin (Δ[1] : SSet.{u})) Y).right).inv ≫
      j ▷ (PointedObject.basedHom (PointedObject.adjoin (Δ[1] : SSet.{u})) Y).right ≫
        evaluation (Δ[1] : SSet.{u}) Y) = _
  rw [evaluation_at_unit]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint, endpoint_eq_map]

/-- 始点評価は、通常のホモトピーの同じ零端点での評価。 -/
lemma square_zero {A : SSet.{u}} {Y : PointedSimplicialSet.{u}}
    (F : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) :
    SSet.ι₀ ≫ square F = F ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right := by
  have h := square_face F (1 : Fin 2)
  rw [stdSimplex.δ_one_eq_const, SSet.comp_const] at h
  exact h

/-- 終点評価も、通常のホモトピーの同じ一端点での評価。 -/
lemma square_one {A : SSet.{u}} {Y : PointedSimplicialSet.{u}}
    (F : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) :
    SSet.ι₁ ≫ square F = F ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right := by
  have h := square_face F (0 : Fin 2)
  rw [stdSimplex.δ_zero_eq_const, SSet.comp_const] at h
  exact h

/-- 自由 path の同じ二変数射は、元の二つの端点射を結ぶ通常の実ホモトピー。 -/
def homotopy {A : SSet.{u}} {Y : PointedSimplicialSet.{u}}
    (F : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) :
    SSet.Homotopy (F ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right)
      (F ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right) where
  h := square F
  h₀ := square_zero F
  h₁ := square_one F
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- パラメータへの前合成は、同じ二次元評価射への前合成として計算される。 -/
lemma square_pre {A D : SSet.{u}} {Y : PointedSimplicialSet.{u}}
    (F : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace Y).right) (a : D ⟶ A) :
    a ▷ (Δ[1] : SSet.{u}) ≫ square F = square (a ≫ F) := by
  rw [square, square, braiding_naturality_left_assoc,
    ← uncurry_natural_left, Category.assoc]

/-- 定数 path 族の評価は、パラメータ方向の射影に同じ元の族を合成したもの。 -/
lemma square_constant {A : SSet.{u}} {Y : PointedSimplicialSet.{u}} (a : A ⟶ Y.right) :
    square (a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Y).right) = fst A (Δ[1] : SSet.{u}) ≫ a := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u} =
      PointedWeightedEnd.weightCollapse (Δ[1] : SSet.{u}) := by
    change PointedObject.adjoinFunctor.map (toUnit (Δ[1] : SSet.{u})) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  have hf : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Y =
      PointedWeightedEnd.constantFamily (Δ[1] : SSet.{u}) Y := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath, he, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    rfl
  have hc : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Y).right ≫
      FreePointedHomRestriction.restrict (Δ[1] : SSet.{u}) Y =
        curry (snd (Δ[1] : SSet.{u}) Y.right) := by
    rw [hf]
    exact PointedWeightedEnd.constantFamily_restrict (Δ[1] : SSet.{u}) Y
  rw [square, Category.assoc, hc, uncurry_natural_left, uncurry_curry]
  rw [← braiding_naturality_left_assoc]
  rfl

end SerrePositivity.KST.Spectra.FreePathEvaluation
