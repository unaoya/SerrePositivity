module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.SmallKanRealization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence

/-!
概要：局所 Kan な単体的圏の共変表現可能関手と、その全 coherent 実現。
方針：豊穣合成の転置を作用とし、合成則を単体ごとの結合則で検証する。
規約：元の Hom と全高次作用を保持する。
使われ方：HTT 5.1.3 の共変 Hom 比較の入力。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

variable {D : Type v} [Category.{u} D] [SimplicialCategory D]

/-- 豊穣後合成の転置。 -/
def representableHomAction (x y z : D) :
    SimplicialCategory.sHom y z ⟶
      (ihom (SimplicialCategory.sHom x y)).obj (SimplicialCategory.sHom x z) :=
  curry (eComp SSet x y z)

lemma representableHomAction_id (x y : D) :
    eId SSet y ≫ representableHomAction x y y =
      MonoidalClosed.id (SimplicialCategory.sHom x y) := by
  apply uncurry_injective
  rw [representableHomAction, uncurry_natural_left, uncurry_curry,
    MonoidalClosed.id_eq, uncurry_curry]
  apply (cancel_epi (ρ_ (SimplicialCategory.sHom x y)).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id] using (e_comp_id SSet x y)

lemma representableHomAction_comp (x y z w : D) :
    eComp SSet y z w ≫ representableHomAction x y w =
      (representableHomAction x y z ⊗ₘ representableHomAction x z w) ≫
        MonoidalClosed.comp (SimplicialCategory.sHom x y)
          (SimplicialCategory.sHom x z) (SimplicialCategory.sHom x w) := by
  apply uncurry_injective
  rw [representableHomAction, uncurry_natural_left, uncurry_curry]
  rw [uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    MonoidalClosed.compTranspose_eq]
  dsimp only [representableHomAction]
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc]
  have exchange := whisker_exchange
    ((ihom.ev (SimplicialCategory.sHom x y)).app (SimplicialCategory.sHom x z))
    (curry (eComp SSet x z w))
  dsimp only [Functor.comp_obj, tensorLeft, curriedTensor, Functor.id_obj] at exchange
  rw [reassoc_of% exchange]
  simp only [← comp_whiskerRight_assoc, ← uncurry_eq, uncurry_curry]
  exact (e_assoc SSet x y z w).symm

/-- 固定した始点からの元の Kan Hom を束ねる豊穣関手。 -/
def representableHomFunctor [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)]
    (x : D) : EnrichedFunctor SSet.{u} D _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj y := ⟨SimplicialCategory.sHom x y, inferInstance⟩
  map y z := representableHomAction x y z
  map_id y := representableHomAction_id x y
  map_comp y z w := representableHomAction_comp x y z w

/-- 対象の値は元の Kan Hom そのもの。 -/
lemma representableHomFunctor_obj
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)] (x y : D) :
    ((representableHomFunctor x).obj y).obj = SimplicialCategory.sHom x y := rfl

/-- 全高次の作用は元の豊穣合成の curry。 -/
lemma representableHomFunctor_map
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)] (x y z : D) :
    (representableHomFunctor x).map y z = curry (eComp SSet x y z) := rfl

/-- 小さい coherent nerve 上の全表現可能図式。 -/
def representableHomCoherent {D : Type u} [Category.{u} D] [SimplicialCategory D]
    [∀ a b : D, KanComplex (SimplicialCategory.sHom a b)] (x : D) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialNerve D) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.smallKanRealization (representableHomFunctor x)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
