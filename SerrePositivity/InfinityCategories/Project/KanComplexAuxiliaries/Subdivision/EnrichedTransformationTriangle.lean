module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedOrderedCylinder
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedUnitTransformationHom

/-!
概要：因子分解を持つ豊穣自然変換から、三段の円柱上の実際の豊穣関手を作る。
方針：段の間の Hom には自然変換の合成作用を使い、因子分解の式を三段をまたぐ合成に使う。
規約：全 Hom パラメータの合成保存を証明する。使われ方：零評価の coherent な三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
end SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle
open _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  (F G H : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
  (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H)
  (ζ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F H)

/-- 三つの段に元の三つの豊穣関手を置く。 -/
def stage (i : Fin 3) : EnrichedFunctor SSet.{u} C D :=
  if i = 0 then F else if i = 1 then G else H

/-- 三段の円柱の対象の像。 -/
def obj (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) C) : D :=
  (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.stage F G H X.position).obj X.val

/-- 同じ段では元の Hom、段の間では指定した自然変換で送る。 -/
def map : (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) C) →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.hom X Y ⟶ (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H X ⟶[SSet] _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H Y)
  | ⟨⟨0, _⟩, x⟩, ⟨⟨0, _⟩, y⟩ => snd _ _ ≫ F.map x y
  | ⟨⟨0, _⟩, x⟩, ⟨⟨1, _⟩, y⟩ => snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom η x y
  | ⟨⟨0, _⟩, x⟩, ⟨⟨2, _⟩, y⟩ => snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom ζ x y
  | ⟨⟨1, _⟩, x⟩, ⟨⟨0, _⟩, y⟩ =>
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.eliminateHom _ _ (by intro h; change (1 : ℕ) ≤ 0 at h; omega) _
  | ⟨⟨1, _⟩, x⟩, ⟨⟨1, _⟩, y⟩ => snd _ _ ≫ G.map x y
  | ⟨⟨1, _⟩, x⟩, ⟨⟨2, _⟩, y⟩ => snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom θ x y
  | ⟨⟨2, _⟩, x⟩, ⟨⟨0, _⟩, y⟩ =>
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.eliminateHom _ _ (by intro h; change (2 : ℕ) ≤ 0 at h; omega) _
  | ⟨⟨2, _⟩, x⟩, ⟨⟨1, _⟩, y⟩ =>
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.eliminateHom _ _ (by intro h; change (2 : ℕ) ≤ 1 at h; omega) _
  | ⟨⟨2, _⟩, x⟩, ⟨⟨2, _⟩, y⟩ => snd _ _ ≫ H.map x y
  | ⟨⟨n + 3, hn⟩, _⟩, _ => False.elim (by omega)
  | _, ⟨⟨n + 3, hn⟩, _⟩ => False.elim (by omega)

/-- 各段の恒等射は元の恒等射へ送られる。 -/
lemma map_id (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.identity X ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map F G H η θ ζ X X = eId SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H X) := by
  rcases X with ⟨i, x⟩
  fin_cases i
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app (F.map_id x) d) PUnit.unit
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app (G.map_id x) d) PUnit.unit
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app (H.map_id x) d) PUnit.unit

/-- 三段の合成は、成分での因子分解と全 Hom の自然性によって保たれる。 -/
lemma map_comp
    (hc : ∀ X, ζ.app X = (λ_ (𝟙_ SSet.{u})).inv ≫
      (η.app X ⊗ₘ θ.app X) ≫ eComp SSet (F.obj X) (G.obj X) (H.obj X))
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.composition X Y Z ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map F G H η θ ζ X Z =
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map F G H η θ ζ X Y ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map F G H η θ ζ Y Z) ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H X) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H Y) (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H Z) := by
  rcases X with ⟨i, x⟩
  rcases Y with ⟨j, y⟩
  rcases Z with ⟨k, z⟩
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨p, f⟩, ⟨q, g⟩⟩
    let fg : ((x ⟶[SSet] y) ⊗ (y ⟶[SSet] z)).obj d := (f, g)
    solve
    | have hp := p.down.down
      norm_num [Fin.le_def] at hp
    | have hq := q.down.down
      norm_num [Fin.le_def] at hq
    | exact ConcreteCategory.congr_hom (NatTrans.congr_app (F.map_comp x y z) d) fg
    | exact ConcreteCategory.congr_hom (NatTrans.congr_app (G.map_comp x y z) d) fg
    | exact ConcreteCategory.congr_hom (NatTrans.congr_app (H.map_comp x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_left η x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_right η x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_left θ x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_right θ x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_left ζ x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_right ζ x y z) d) fg
    | exact ConcreteCategory.congr_hom
        (NatTrans.congr_app
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedUnitTransformationHom.hom_comp_factorization η θ ζ hc x y z) d) fg

/-- 成分での因子分解を、全ての高次の Hom を含む三段の円柱の関手へ実現する。 -/
def functor
    (hc : ∀ X, ζ.app X = (λ_ (𝟙_ SSet.{u})).inv ≫
      (η.app X ⊗ₘ θ.app X) ≫ eComp SSet (F.obj X) (G.obj X) (H.obj X)) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) C) D where
  obj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj F G H
  map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map F G H η θ ζ
  map_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map_id F G H η θ ζ
  map_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map_comp F G H η θ ζ hc

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.functor := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map_comp := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map_id := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map_id

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.obj := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.obj

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.stage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.stage := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.stage

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map._proof_10 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map._proof_8

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.map.match_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.map.match_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedTransformationTriangle.stage._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.stage._proof_1
