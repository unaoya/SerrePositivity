module
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import SerrePositivity.InfinityCategories.F1.QuasicategoryEnrichedDiagramOrdinaryFunctor
public import SerrePositivity.KST.SConstruction.QuasicategoryEnrichedDiagramPrecomposition

/-! # 単体的図式全体の標準豊穣 Hom
概要：同じ単体的図式を、全ての面退化に自然な標準 end の Hom で豊穣化する。
方針：Mathlib の関手圏の豊穣構造と、小さい単体圏上の既存の全極限を使う。
規約：外側の既定豊穣と区別し、添字の宇宙は保つ。使われ方：実 S• の native 入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories

local instance simplicialDiagramBase_enrichedCategory :
    EnrichedCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedCategorySelf SSet.{u}
local instance simplicialDiagramBase_enrichedOrdinaryCategory :
    EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}

/-- 同じ実単体的図式を保持し、内側のパラメータ作用を選ぶための対象。 -/
structure SimplicialSSetDiagram where
  diagram : SimplicialObject SSet.{u}

/-- 通常の射は、元の同じ単体的図式間の自然変換。 -/
instance simplicialSSetDiagram_category : Category.{u} SimplicialSSetDiagram.{u} where
  Hom X Y := X.diagram ⟶ Y.diagram
  id X := 𝟙 X.diagram
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- Hom は全ての面退化に自然な標準 end であり、native パラメータは内側に作用する。 -/
instance simplicialSSetDiagram_simplicialCategory :
    SimplicialCategory SimplicialSSetDiagram.{u} where
  Hom X Y := Enriched.FunctorCategory.enrichedHom SSet X.diagram Y.diagram
  id X := Enriched.FunctorCategory.enrichedId SSet X.diagram
  comp X Y Z := Enriched.FunctorCategory.enrichedComp SSet X.diagram Y.diagram Z.diagram
  id_comp X Y := Enriched.FunctorCategory.enriched_id_comp SSet X.diagram Y.diagram
  comp_id X Y := Enriched.FunctorCategory.enriched_comp_id SSet X.diagram Y.diagram
  assoc W X Y Z := Enriched.FunctorCategory.enriched_assoc SSet
    W.diagram X.diagram Y.diagram Z.diagram
  homEquiv := Enriched.FunctorCategory.homEquiv SSet
  homEquiv_id X := Enriched.FunctorCategory.homEquiv_id SSet X.diagram
  homEquiv_comp f g := Enriched.FunctorCategory.homEquiv_comp SSet f g

/-- 豊穣構造だけを忘れると、元の同じ図式と同じ通常の自然変換になる。 -/
def simplicialSSetDiagramForget : SimplicialSSetDiagram.{u} ⥤ SimplicialObject SSet.{u} where
  obj X := X.diagram
  map f := f
  map_id _X := rfl
  map_comp _f _g := rfl

/-- 内側の標準 end の Hom から、同じ一段の元の内部 Hom への実射影。 -/
def simplicialSSetDiagramProjection (X Y : SimplicialSSetDiagram.{u})
    (n : SimplexCategoryᵒᵖ) :
    (X ⟶[SSet.{u}] Y) ⟶ (ihom (X.diagram.obj n)).obj (Y.diagram.obj n) :=
  Enriched.FunctorCategory.enrichedHomπ SSet X.diagram Y.diagram n

/-- 図式全体の豊穣 Hom の射は、元の全ての段への射影で一意に定まる。 -/
lemma simplicialSSetDiagramHom_ext {P : SSet.{u}} {X Y : SimplicialSSetDiagram.{u}}
    {f g : P ⟶ (X ⟶[SSet.{u}] Y)}
    (h : ∀ n, f ≫ simplicialSSetDiagramProjection X Y n =
      g ≫ simplicialSSetDiagramProjection X Y n) : f = g := by
  apply Limits.end_.hom_ext
  exact h

/-- 元の通常の自然変換の豊穣表示は、各段で同じ元の成分の curry を回収する。 -/
lemma simplicialSSetDiagramHomEquiv_projection {X Y : SimplicialSSetDiagram.{u}}
    (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    eHomEquiv SSet.{u} f ≫ simplicialSSetDiagramProjection X Y n =
      curry' ((show X.diagram ⟶ Y.diagram from f).app n) :=
  Enriched.FunctorCategory.homEquiv_apply_π SSet f n

/-- 全高次比較の評価自然性は、同じ内部 Hom の前後合成の自然性と一致する。 -/
lemma quasicategoryEnrichedComparison_internal_naturality
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C QuasicategoryObject.{u}}
    (η : QuasicategoryEnrichedComparison F G) (X Y : C) :
    F.map X Y ≫ (ihom (F.obj X).obj).map (η.val Y) =
      G.map X Y ≫ (pre (η.val X)).app (G.obj Y).obj := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  exact (η.property X Y).symm

end SerrePositivity.KST.SConstruction
