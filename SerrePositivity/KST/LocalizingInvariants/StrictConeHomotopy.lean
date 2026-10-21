module

public import SerrePositivity.KST.LocalizingInvariants.StrictConePrismComponent
public import SerrePositivity.InfinityCategories.Stable.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.F2.HomotopySimplexFaces

/-!
概要：通常の錐の全比較から、元の二つの strict coherent 錐を結ぶ実ホモトピーを作る。
方針：始対象を加えた関手の prism を、同じ join の標準錐で制限する。
規約：頂点射も基底の比較も全 prism に保持。使われ方：BF fiber の実 cube の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F2
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants.StrictConeMap

def shape (I : Type u) [SmallCategory I] :
    join (Δ[0] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj (nerve I)) ⟶
      nerve (WithInitial (AsSmall.{v} I)) :=
  joinMap (𝟙 Δ[0]) ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
    nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I))

lemma shape_inl (I : Type u) [SmallCategory I] :
    joinInl (Δ[0] : SSet.{max u v}) _ ≫ shape.{u, v} I =
      nervePoint (WithInitial.star : WithInitial (AsSmall.{v} I)) := by
  rw [shape, ← Category.assoc, joinInl_joinMap, Category.id_comp, nerveInitialCone_left]

lemma shape_vertex (I : Type u) [SmallCategory I] :
    (shape.{u, v} I).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (joinInl Δ[0] _)) =
      ComposableArrows.mk₀ (WithInitial.star : WithInitial (AsSmall.{v} I)) := by
  rw [← SSet.yonedaEquiv_comp, shape_inl]
  rfl

lemma precomp_component {A B X : SSet.{u}} (i : A ⟶ B) {F G : B ⟶ X}
    (H : SSet.Homotopy F G) (x : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (stableHomotopyPrecomp i H) x).edge =
      (simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) x)).edge := by
  rw [homotopyVertexEdge_simplex, homotopyVertexEdge_simplex]
  change H.h.app (Opposite.op ⦋1⦌) (i.app _ (A.σ 0 x), _) =
    H.h.app (Opposite.op ⦋1⦌) (B.σ 0 (i.app _ x), _)
  exact congrArg (fun z ↦ H.h.app (Opposite.op ⦋1⦌)
    (z, SSet.yonedaEquiv (𝟙 Δ[1])))
      (ConcreteCategory.congr_hom (i.naturality (SimplexCategory.σ 0).op) x)

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] {F G : I ⥤ C} (η : F ⟶ G) (c : Cone F) (d : Cone G)
  (m : c.pt ⟶ d.pt) (hm : ∀ i, c.π.app i ≫ η.app i = m ≫ d.π.app i)

def homotopy : SSet.Homotopy (strictCoherentCone c).val (strictCoherentCone d).val :=
  stableHomotopyPrecomp (shape I) (largeHomotopy (transformation η c d m hm))

lemma homotopy_apex :
    (simplicialHomotopyVertexEdge (homotopy η c d m hm)
      (SSet.yonedaEquiv (joinInl Δ[0] _))).edge = (coherentNerveEdge m).edge := by
  rw [homotopy, precomp_component, shape_vertex, largeHomotopy_component]
  rfl

end SerrePositivity.KST.LocalizingInvariants.StrictConeMap
