module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanComparisonNerves
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve

/-!
概要：局所 Kan な単体的圏の同じ豊穣 Hom を空間値の豊穣関手に束ねる。
方針：元の合成の curry を作用とし、元の単位・結合律を使う。
規約：全高次 Hom の作用を保持し、頂点の比較だけから自然性を推論しない。
使われ方：hammock の strict Hom 図式と Yoneda 側の全比較の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
variable {D : Type v} [Category.{u} D] [SimplicialCategory D]
  [∀ A B : D, KanComplex (SimplicialCategory.sHom A B)] (X : D)

/-- 概要：同じ元の合成を使う共変豊穣 Hom 関手。
方針：合成の curry に元の単位・結合律を代入する。
規約：対象は元の Kan Hom、全 Hom 単体の作用を保持する。
使われ方：coherent nerve 上の元の共変 Hom 図式。
-/
def enrichedHomFunctor : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj Y := ⟨SimplicialCategory.sHom X Y, inferInstance⟩
  map Y Z := curry (SimplicialCategory.sHomComp X Y Z)
  map_id Y := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    change (SimplicialCategory.sHom X Y) ◁ eId SSet Y ≫ eComp SSet X Y Y =
      (ρ_ (SimplicialCategory.sHom X Y)).hom
    calc
      _ = (ρ_ _).hom ≫ ((ρ_ _).inv ≫ _ ◁ eId SSet Y ≫ eComp SSet X Y Y) := by
        simp only [Iso.hom_inv_id_assoc]
      _ = _ := by rw [e_comp_id, Category.comp_id]
  map_comp Y Z W := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    change (SimplicialCategory.sHom X Y) ◁ eComp SSet Y Z W ≫ eComp SSet X Y W =
      uncurry ((curry (eComp SSet X Y Z) ⊗ₘ curry (eComp SSet X Z W)) ≫
        MonoidalClosed.comp (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom X Z)
          (SimplicialCategory.sHom X W))
    rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
      MonoidalClosed.compTranspose_eq]
    rw [tensorHom_def, whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc]
    have hx := whisker_exchange
      ((ihom.ev (SimplicialCategory.sHom X Y)).app (SimplicialCategory.sHom X Z))
      (curry (eComp SSet X Z W))
    dsimp only [Functor.comp_obj, tensorLeft, curriedTensor, Functor.id_obj] at hx
    rw [reassoc_of% hx, ← comp_whiskerRight_assoc, ← uncurry_eq, uncurry_curry,
      ← uncurry_eq, uncurry_curry]
    exact (e_assoc SSet X Y Z W).symm

/-- 概要：同じ豊穣 Hom 関手の底は元の Hom そのもの。
方針：定義の対象成分を読む。
規約：厳密な等式。使われ方：原本の Yoneda 比較への代入。 -/
lemma enrichedHomFunctor_obj (Y : D) :
    ((enrichedHomFunctor X).obj Y).obj = SimplicialCategory.sHom X Y := rfl

/-- 概要：同じ豊穣 Hom 関手の高次作用は元の合成の curry。
方針：定義の Hom 成分を読む。
規約：全単体の実射。使われ方：Yoneda 側の同じ比較の入力の照合。 -/
lemma enrichedHomFunctor_map (Y Z : D) :
    (enrichedHomFunctor X).map Y Z = curry (eComp SSet X Y Z) := rfl

end SerrePositivity.EInfinity.FrameHom
