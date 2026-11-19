module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalIndexPrism

/-!
概要：指定区間の下の余錐を、同じ図式を持つ錐の辺に直し、四つの境界を計算する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open BraidedCategory MonoidalClosed
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma pointInterval_fst
    (i : Fin 2) :
    (stdSimplex.δ i ▷ (Δ[0] : SSet.{u})) ≫ fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) =
      snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ stdSimplex.δ i := by
  ext n ⟨a, b⟩
  have h : a = b := by
    apply stdSimplex.ext
    intro j
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
  subst a
  rfl

private lemma movingConePrism_preEndpoint
    (J : SSet.{u}) (i : Fin 2) :
    (stdSimplex.δ i ▷ join (Δ[0] : SSet.{u}) J) ≫
        joinTensorLeft (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) J ≫
          joinMap (fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u})) (𝟙 J) =
      snd (Δ[0] : SSet.{u}) (join (Δ[0] : SSet.{u}) J) ≫ joinMap (stdSimplex.δ i) (𝟙 J) := by
  rw [← Category.assoc, joinTensorLeft_naturality, Category.assoc,
    ← joinMap_comp, pointInterval_fst, Category.id_comp]
  rw [show joinMap (snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ stdSimplex.δ i) (𝟙 J) =
      joinMap (snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u})) (𝟙 J) ≫
        joinMap (stdSimplex.δ i) (𝟙 J) from by
          simpa only [Category.id_comp] using
            joinMap_comp (snd (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}))
              (stdSimplex.δ i) (𝟙 J) (𝟙 J)]
  rw [← Category.assoc, joinTensorLeft_unit]

/-- 区間の下の指定余錐を、固定添字の錐の辺として表示する。 -/
def movingConePrism {J X : SSet.{u}} {η : (Δ[1] : SSet.{u}) ⟶ X}
    (w : J ⟶ sliceUnder η) :
    join (Δ[0] : SSet.{u}) J ⊗ (Δ[1] : SSet.{u}) ⟶ X :=
  (β_ _ _).hom ≫ joinTensorLeft (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) J ≫
    joinMap (fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u})) (𝟙 J) ≫ sliceUnderUncurry w

private lemma movingConePrism_diagram {J X : SSet.{u}} {η : (Δ[1] : SSet.{u}) ⟶ X}
    (w : J ⟶ sliceUnder η) :
    (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ movingConePrism w =
      fst J (Δ[1] : SSet.{u}) ≫ w ≫ sliceUnderProjection η := by
  dsimp only [movingConePrism]
  rw [← Category.assoc, braiding_naturality_left, Category.assoc,
    ← Category.assoc (Δ[1] ◁ joinInr (Δ[0] : SSet.{u}) J), joinTensorLeft_inr]
  simp only [Category.assoc]
  rfl

private lemma movingConePrism_apex {J X : SSet.{u}} {η : (Δ[1] : SSet.{u}) ⟶ X}
    (w : J ⟶ sliceUnder η) :
    (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ movingConePrism w =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ η := by
  dsimp only [movingConePrism]
  rw [← Category.assoc, braiding_naturality_left, Category.assoc,
    ← Category.assoc (Δ[1] ◁ joinInl (Δ[0] : SSet.{u}) J), joinTensorLeft_inl]
  simp only [Category.assoc, joinInl_joinMap, ← Category.assoc (joinInl _ _),
    sliceUnderUncurry_fixed]
  rfl

private lemma movingConePrism_zero {J X : SSet.{u}} {η : (Δ[1] : SSet.{u}) ⟶ X}
    (w : J ⟶ sliceUnder η) :
    (SSet.ι₀ : join (Δ[0] : SSet.{u}) J ⟶ _) ≫ movingConePrism w =
      joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w := by
  let A := join (Δ[0] : SSet.{u}) J
  have h : snd (Δ[0] : SSet.{u}) A ≫ (SSet.ι₀ : A ⟶ _) ≫ (β_ A (Δ[1] : SSet.{u})).hom =
      stdSimplex.δ (1 : Fin 2) ▷ A := by
    apply SSet.hom_ext
    intro k
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      change (0 : Fin 2) = (SimplexCategory.δ (1 : Fin 2)).toOrderHom ((stdSimplex.objEquiv a).toOrderHom j)
      rw [Fin.eq_zero ((stdSimplex.objEquiv a).toOrderHom j)]
      rfl
    · rfl
  apply (cancel_epi (snd (Δ[0] : SSet.{u}) A)).mp
  let Q := joinTensorLeft (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) J ≫
    joinMap (fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u})) (𝟙 J)
  change snd _ A ≫ SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫ _ =
    snd _ A ≫ joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w
  calc
    _ = (snd (Δ[0] : SSet.{u}) A ≫ SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom) ≫
        Q ≫ sliceUnderUncurry w := by simp only [Q, Category.assoc]
    _ = (stdSimplex.δ (1 : Fin 2) ▷ A) ≫ Q ≫ sliceUnderUncurry w :=
      congrArg (fun f => f ≫ Q ≫ sliceUnderUncurry w) h
    _ = _ := by
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ sliceUnderUncurry w)
        (movingConePrism_preEndpoint J (1 : Fin 2))

private lemma movingConePrism_one {J X : SSet.{u}} {η : (Δ[1] : SSet.{u}) ⟶ X}
    (w : J ⟶ sliceUnder η) :
    (SSet.ι₁ : join (Δ[0] : SSet.{u}) J ⟶ _) ≫ movingConePrism w =
      joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w := by
  let A := join (Δ[0] : SSet.{u}) J
  have h : snd (Δ[0] : SSet.{u}) A ≫ (SSet.ι₁ : A ⟶ _) ≫ (β_ A (Δ[1] : SSet.{u})).hom =
      stdSimplex.δ (0 : Fin 2) ▷ A := by
    apply SSet.hom_ext
    intro k
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      change (1 : Fin 2) = (SimplexCategory.δ (0 : Fin 2)).toOrderHom ((stdSimplex.objEquiv a).toOrderHom j)
      rw [Fin.eq_zero ((stdSimplex.objEquiv a).toOrderHom j)]
      rfl
    · rfl
  apply (cancel_epi (snd (Δ[0] : SSet.{u}) A)).mp
  let Q := joinTensorLeft (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) J ≫
    joinMap (fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u})) (𝟙 J)
  change snd _ A ≫ SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫ _ =
    snd _ A ≫ joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w
  calc
    _ = (snd (Δ[0] : SSet.{u}) A ≫ SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom) ≫
        Q ≫ sliceUnderUncurry w := by simp only [Q, Category.assoc]
    _ = (stdSimplex.δ (0 : Fin 2) ▷ A) ≫ Q ≫ sliceUnderUncurry w :=
      congrArg (fun f => f ≫ Q ≫ sliceUnderUncurry w) h
    _ = _ := by
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ sliceUnderUncurry w)
        (movingConePrism_preEndpoint J (0 : Fin 2))

/-- 指定区間の下の余錐を、同じ図式を持つ錐の辺に直し、四つの境界を計算する。
Kerodon §4.6.6（Tag 04J1）の join と直積の比較。HTT 5.1.5.6 の指定右 Kan 比較で使う境界式。 -/
lemma movingConePrism_boundaries
    {J X : SSet.{u}} {η : (Δ[1] : SSet.{u}) ⟶ X}
    (w : J ⟶ sliceUnder η) :
    (SSet.ι₀ : join (Δ[0] : SSet.{u}) J ⟶ _) ≫ movingConePrism w =
      joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w ∧
    (SSet.ι₁ : join (Δ[0] : SSet.{u}) J ⟶ _) ≫ movingConePrism w =
      joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w ∧
    (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ movingConePrism w =
      fst J (Δ[1] : SSet.{u}) ≫ w ≫ sliceUnderProjection η ∧
    (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ movingConePrism w =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ η := by
  exact ⟨movingConePrism_zero w, movingConePrism_one w, movingConePrism_diagram w,
    movingConePrism_apex w⟩

end SerrePositivity.InfinityCategories.Sheaves
