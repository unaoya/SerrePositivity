module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderNervePair

/-!
概要：パラメータ円柱を元の圏の一対象で評価する豊穣関手と、nerve の pairing の制限。
方針：元の Hom を恒等へ送る定値豊穣関手を用い、同じ対象の左右のコピーを保持する。
規約：全高次単体での厳密等式。使われ方：円の評価三角形を実際の普遍評価へ照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
section
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 全ての Hom を単位を介して指定した対象の恒等へ送る、定値豊穣関手。 -/
def constantFunctor (T : Type w) [EnrichedCategory SSet.{u} T] (X : C) :
    EnrichedFunctor SSet.{u} T C where
  obj _ := X
  map _ _ := toUnit _ ≫ eId SSet X
  map_id _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  map_comp _ _ _ := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    exact (base_id_comp_app X X d ((eId SSet X).app d PUnit.unit)).symm

/-- 二対象のパラメータ円柱を、元の一対象の左右のコピーへ送る。 -/
def fiberEnriched (A : SSet.{u}) (X : C) :
    EnrichedFunctor SSet.{u} (Object A Point.{v}) (Object A C) :=
  pairFunctor A (constantFunctor (Object A Point.{v}) X) (EnrichedFunctor.id SSet _)

/-- 一対象上の円柱の cross Hom は、元の対象の恒等族を厳密に保持する。 -/
lemma fiberEnriched_cross (A : SSet.{u}) (X : C) :
    (ρ_ A).inv ≫ (fiberEnriched A X).map
        (⟨false, ⟨PUnit.unit⟩⟩ : Object A Point.{v}) ⟨true, ⟨PUnit.unit⟩⟩ =
      crossIdentity A X := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- pairing を元の対象の標準頂点へ制限すると、一対象の円柱の nerve そのもの。 -/
lemma nervePair_fiber (A : SSet.{u}) (X : C) :
    lift (SSet.const (coherentNerveVertex X))
        (𝟙 (SimplicialNerve (Object A Point.{v}))) ≫ nervePair A =
      coherentNerveMap (fiberEnriched A X) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro G
  refine EnrichedFunctor.ext SSet ?_ ?_
  · intro a
    rfl
  intro a b
  change pairBySide A (G.obj a).side (G.obj b).side (G.map a b)
      (toUnit _ ≫ eId SSet X) ≫ 𝟙 _ =
    G.map a b ≫ pairBySide A (G.obj a).side (G.obj b).side (𝟙 _)
      (toUnit _ ≫ eId SSet X)
  rw [Category.comp_id, pairBySide_precomp]
  rfl

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
