module


public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderEndpoints

/-!
概要：パラメータの射が誘導する豊穣円柱の制限。
方針：同じ端の Hom は恒等、端をまたぐ Hom ではパラメータだけを送る。
規約：元の対象・写像のパラメータを保つ。使われ方：円の評価の基点と両端の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable {A B : SSet.{u}} {C : Type v} [EnrichedCategory SSet.{u} C] (i : A ⟶ B)

/-- パラメータの変更は端と元の対象を保つ。 -/
def restrictionObject (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object B C := ⟨X.side, X.val⟩

/-- 端をまたぐ Hom のパラメータだけを変更する射。 -/
def restrictionMap : (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A X Y ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom B (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject Y)
  | ⟨false, _⟩, ⟨false, _⟩ => 𝟙 _
  | ⟨false, _⟩, ⟨true, _⟩ => i ⊗ₘ 𝟙 _
  | ⟨true, _⟩, ⟨false, _⟩ => 𝟙 _
  | ⟨true, _⟩, ⟨true, _⟩ => 𝟙 _

/-- パラメータの変更は円柱の豊穣恒等射を保つ。 -/
lemma restrictionMap_id (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity A X ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap i X X = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity B (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject X) := by
  rcases X with ⟨s, x⟩
  cases s <;> exact Category.comp_id _

/-- パラメータの変更は円柱の豊穣合成を保つ。 -/
lemma restrictionMap_comp (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap i X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap i X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap i Y Z) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition B (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject Y) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject Z) := by
  rcases X with ⟨s, x⟩
  rcases Y with ⟨t, y⟩
  rcases Z with ⟨r, z⟩
  cases s <;> cases t <;> cases r
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
  · rfl
  · rfl
  · exact b.elim
  · rfl
  · exact a.elim
  · exact a.elim
  · exact b.elim
  · rfl

/-- パラメータの射が誘導する、実際の豊穣円柱の関手。 -/
def restriction : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object B C) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionObject
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap i
  map_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap_id i
  map_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restrictionMap_comp i

variable {D : Type w} [EnrichedCategory SSet.{u} D]
  (F G : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj A) F G)
  (θ : GradedNatTrans (Center.ofBraidedObj B) F G)

/-- パラメータの射による豊穣自然変換の制限。 -/
def gradedRestriction : GradedNatTrans (Center.ofBraidedObj A) F G where
  app X := i ≫ θ.app X
  naturality X Y := by
    have h := congrArg (fun f ↦ i ▷ (X ⟶[SSet] Y) ≫ f) (θ.naturality X Y)
    change i ▷ (X ⟶[SSet] Y) ≫ (β_ B (X ⟶[SSet] Y)).hom ≫
      (F.map X Y ⊗ₘ θ.app Y) ≫ eComp SSet _ _ _ = _ at h
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left] at h
    simp only [Category.assoc] at h
    rw [whiskerLeft_comp_tensorHom_assoc, whiskerRight_comp_tensorHom_assoc] at h
    exact h

/-- 評価のパラメータ制限は、円柱の関手の前合成と厳密に可換。 -/
lemma restriction_evaluation (h : ∀ X, i ≫ θ.app X = η.app X) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction (C := C) i).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor B F G θ) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor A F G η := by
  apply EnrichedFunctor.ext SSet
    (F := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction (C := C) i).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor B F G θ))
    (G := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor A F G η)
    (fun X ↦ by rcases X with ⟨s, x⟩; cases s <;> rfl)
  rintro ⟨s, x⟩ ⟨t, y⟩
  cases s <;> cases t
  · change ((𝟙 _ ≫ F.map x y) ≫ 𝟙 _) = F.map x y
    simp
  · change ((i ⊗ₘ 𝟙 _) ≫ (θ.app x ⊗ₘ G.map x y) ≫ eComp SSet _ _ _) ≫ 𝟙 _ = _
    rw [Category.comp_id, tensorHom_comp_tensorHom_assoc, h, Category.id_comp]
    rfl
  · change ((𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.emptyTo _) ≫ 𝟙 _) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.emptyTo _
    simp
  · change ((𝟙 _ ≫ G.map x y) ≫ 𝟙 _) = G.map x y
    simp

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
