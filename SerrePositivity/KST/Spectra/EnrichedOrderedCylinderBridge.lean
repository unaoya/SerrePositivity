module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderReindex
public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderNervePair

/-!
概要：二段の順序付き円柱を、指定したパラメータの辺で二対象の円柱へ送る。
方針：同じ段では Hom の射影、段をまたぐ場合は指定した単位パラメータを添える。
規約：全 Hom で合成を保存する。使われ方：基点評価の辺と三角形の外辺の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {A : SSet.{u}} (i : 𝟙_ SSet.{u} ⟶ A)

/-- 二段の順序付き円柱の段を、二対象の円柱の両端へ送る。 -/
def bridgeObject (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2) C) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C :=
  ⟨X.position != 0, X.val⟩

/-- 指定した単位パラメータを添える、二段の円柱の Hom の写像。 -/
def bridgeMap : (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2) C) →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.hom X Y ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A (bridgeObject X) (bridgeObject Y)
  | ⟨⟨0, _⟩, _⟩, ⟨⟨0, _⟩, _⟩ => snd _ _
  | ⟨⟨0, _⟩, _⟩, ⟨⟨1, _⟩, _⟩ => lift (toUnit _ ≫ i) (snd _ _)
  | ⟨⟨1, _⟩, _⟩, ⟨⟨0, _⟩, _⟩ =>
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.eliminateHom _ _ (by intro h; change (1 : ℕ) ≤ 0 at h; omega) _
  | ⟨⟨1, _⟩, _⟩, ⟨⟨1, _⟩, _⟩ => snd _ _
  | ⟨⟨n + 2, hn⟩, _⟩, _ => False.elim (by omega)
  | _, ⟨⟨n + 2, hn⟩, _⟩ => False.elim (by omega)

/-- 指定した単位パラメータでの、実際の二段の円柱の比較関手。 -/
def bridge :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 2) C) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  obj := bridgeObject
  map := bridgeMap i
  map_id X := by
    rcases X with ⟨j, x⟩
    fin_cases j <;> rfl
  map_comp X Y Z := by
    rcases X with ⟨j, x⟩
    rcases Y with ⟨k, y⟩
    rcases Z with ⟨l, z⟩
    fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨⟨p, f⟩, ⟨q, g⟩⟩
      solve
      | have hp := p.down.down
        norm_num [Fin.le_def] at hp
      | have hq := q.down.down
        norm_num [Fin.le_def] at hq
      | rfl

end SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
