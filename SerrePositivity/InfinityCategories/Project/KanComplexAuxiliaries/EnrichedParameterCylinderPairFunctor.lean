module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderPairHom

/-!
概要：同じ豊穣源上の図式と二対象の円柱の図式を組み合わせる関手。
方針：対象は端と元の対象、Hom は証明済みの pairing で与える。
規約：豊穣源の前合成と厳密に可換。使われ方：coherent nerve 上の pairing の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable (A : SSet.{u}) {C : Type v} {T : Type w}
  [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} T]
  (F : EnrichedFunctor SSet.{u} T C)
  (G : EnrichedFunctor SSet.{u} T (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}))

/-- 小さい円柱の端と、元の図式の対象を組み合わせる。 -/
def pairObject (X : T) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C := ⟨(G.obj X).side, F.obj X⟩

/-- 小さい円柱のパラメータと、元の図式の全 Hom を組み合わせる。 -/
def pairMap (X Y : T) : (X ⟶[SSet] Y) ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A (G.obj X).side (G.obj Y).side (G.map X Y) (F.map X Y)

/-- pairing は豊穣単位を保つ。 -/
lemma pairMap_id (X : T) :
    eId SSet X ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap A F G X X = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identity A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G X) := by
  change eId SSet X ≫
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A (G.obj X).side (G.obj X).side (G.map X X) (F.map X X) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.identityBySide A (F.obj X ⟶[SSet] F.obj X) (eId SSet (F.obj X)) (G.obj X).side
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_precomp, F.map_id, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_identity]

/-- pairing は豊穣合成を保つ。 -/
lemma pairMap_comp (X Y Z : T) :
    eComp SSet X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap A F G X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap A F G X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap A F G Y Z) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.composition A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G Y) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_comp A (G.obj X).side (G.obj Y).side (G.obj Z).side
    (eComp SSet X Y Z) (eComp SSet (F.obj X) (F.obj Y) (F.obj Z))
    (G.map X Y) (G.map Y Z) (G.map X Z) (F.map X Y) (F.map Y Z) (F.map X Z)
    (G.map_comp X Y Z) (F.map_comp X Y Z)

/-- 共通の豊穣源上での、実際の円柱の pairing 関手。 -/
def pairFunctor : EnrichedFunctor SSet.{u} T (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  obj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject A F G
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap A F G
  map_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap_id A F G
  map_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap_comp A F G

/-- pairing は共通の豊穣源への任意の前合成と厳密に可換。 -/
lemma pairFunctor_precomp {R : Type z} [EnrichedCategory SSet.{u} R]
    (I : EnrichedFunctor SSet.{u} R T) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor A (I.comp SSet F) (I.comp SSet G) = I.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor A F G) := by
  apply EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor A (I.comp SSet F) (I.comp SSet G))
    (G := I.comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor A F G)) (fun _ ↦ rfl)
  intro X Y
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A (G.obj (I.obj X)).side (G.obj (I.obj Y)).side
      (I.map X Y ≫ G.map (I.obj X) (I.obj Y))
      (I.map X Y ≫ F.map (I.obj X) (I.obj Y)) ≫ 𝟙 _ =
    I.map X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide A (G.obj (I.obj X)).side (G.obj (I.obj Y)).side
      (G.map (I.obj X) (I.obj Y)) (F.map (I.obj X) (I.obj Y))
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairBySide_precomp]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairFunctor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairFunctor_precomp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor_precomp

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairMap := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairMap_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairMap_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairMap_id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairObject := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairObject
