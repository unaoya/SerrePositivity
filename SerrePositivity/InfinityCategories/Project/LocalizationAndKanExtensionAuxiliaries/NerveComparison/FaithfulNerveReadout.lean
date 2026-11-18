module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ExtOne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorPostEquivalence

/-!
概要：通常の忠実な nerve への表示があるとき、頂点の一致から同じ引き戻しの相対同型を回収する。
方針：元の相対写像の射影と指定された比較を保つ。
使われ方：R06.2 の始点側の添字比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

private theorem faithful_nerve_map_eq_of_vertices
    {X : SSet.{u}} {C D : Type u} [SmallCategory C] [SmallCategory D]
    (p : C ⥤ D) [p.Faithful] {a b : X ⟶ nerve C}
    (hp : a ≫ nerveMap p = b ≫ nerveMap p)
    (hv : ∀ x : X _⦋0⦌, a.app _ x = b.app _ x) : a = b := by
  apply nerve_hom_ext_one
  intro x
  let A : ComposableArrows C 1 := a.app _ x
  let B : ComposableArrows C 1 := b.app _ x
  have h₀ : A.left = B.left := by
    have h := hv (X.δ 1 x)
    change a.app _ (X.map (SimplexCategory.δ (1 : Fin 2)).op x) =
      b.app _ (X.map (SimplexCategory.δ (1 : Fin 2)).op x) at h
    rw [a.naturality_apply, b.naturality_apply] at h
    exact congrArg (fun t : ComposableArrows C 0 ↦ t.obj 0) h
  have h₁ : A.right = B.right := by
    have h := hv (X.δ 0 x)
    change a.app _ (X.map (SimplexCategory.δ (0 : Fin 2)).op x) =
      b.app _ (X.map (SimplexCategory.δ (0 : Fin 2)).op x) at h
    rw [a.naturality_apply, b.naturality_apply] at h
    exact congrArg (fun t : ComposableArrows C 0 ↦ t.obj 0) h
  have he : A ⋙ p = B ⋙ p :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hp (Opposite.op ⦋1⦌)) x
  apply ComposableArrows.ext₁ h₀ h₁
  apply p.map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_map, Functor.comp_obj]
    using Functor.congr_hom he (homOfLE (show (0 : Fin 2) ≤ 1 by decide))


private theorem relativeFunctorIso_of_faithful_nerve_readout
    {J T B : SSet.{u}} [Quasicategory B] {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (p : C ⥤ D) [p.Faithful] (r : nerve C ⟶ B) [LeftFibration r]
    (s : B ⟶ nerve D) (hs : r ≫ s = nerveMap p)
    (q : T ⟶ B) [LeftFibration q] (h : J ⟶ B)
    (i : T ⟶ nerve C) (hi : i ≫ r = q)
    (ei : IsPrecompositionEquivalence i)
    (a b : J ⟶ T) (ha : a ≫ q = h) (hb : b ≫ q = h)
    (hv : ∀ x : J _⦋0⦌, (a ≫ i).app _ x = (b ≫ i).app _ x) :
    Nonempty (VertexIso (relativeFunctorVertex q h a ha) (relativeFunctorVertex q h b hb)) := by
  let M := relativeFunctorPost q r i hi h
  have he : IsQCatEquivalence M :=
    relativeFunctorPost_isQCatEquivalence_of_precompositionEquivalence q r i hi ei h
  have hp : (a ≫ i) ≫ nerveMap p = (b ≫ i) ≫ nerveMap p := by
    have hproj (t : J ⟶ T) (ht : t ≫ q = h) : (t ≫ i) ≫ nerveMap p = h ≫ s := by
      rw [← hs, ← Category.assoc (t ≫ i), Category.assoc t i r, hi, ht]
    exact (hproj a ha).trans (hproj b hb).symm
  have hh := faithful_nerve_map_eq_of_vertices p hp hv
  have hm : M.app _ (relativeFunctorVertex q h a ha) =
      M.app _ (relativeFunctorVertex q h b hb) := by
    dsimp only [M]
    rw [relativeFunctorPost_vertex, relativeFunctorPost_vertex]
    apply Subtype.ext
    exact congrArg functorVertex hh
  exact ⟨he.isFullyFaithful.preimageVertexIso (eqToIso (congrArg HomotopyCategory.mk hm))⟩


/-- 通常の忠実な nerve への表示があるとき、頂点の一致から同じ引き戻しの相対同型を回収する。
HTT 3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の相対関手空間における同値の反映。 -/
@[cite HTT "3.3.2" (partial := special) "忠実な通常の nerve で比較できる場合の相対関手空間の照合。"]
lemma relativeFunctorIso_of_pullback_nerve_readout
    {J B X T : SSet.{u}} [Quasicategory B] {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (p : C ⥤ D) [p.Faithful] (r : nerve C ⟶ B) [LeftFibration r]
    (s : B ⟶ nerve D) (hs : r ≫ s = nerveMap p)
    (δ : B ⟶ X) (q : T ⟶ X) [LeftFibration q] (h : J ⟶ B)
    (i : pullback q δ ⟶ nerve C) (hi : i ≫ r = pullback.snd q δ)
    (ei : IsPrecompositionEquivalence i)
    (a b : J ⟶ T) (ha : a ≫ q = h ≫ δ) (hb : b ≫ q = h ≫ δ)
    (hv : ∀ x : J _⦋0⦌,
      (pullback.lift a h ha ≫ i).app _ x = (pullback.lift b h hb ≫ i).app _ x) :
    Nonempty (VertexIso (relativeFunctorVertex q (h ≫ δ) a ha)
      (relativeFunctorVertex q (h ≫ δ) b hb)) := by
  let f := pullback.snd q δ
  let _ : LeftFibration f :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := q))⟩
  let l₀ := pullback.lift a h ha
  let l₁ := pullback.lift b h hb
  have h₀ : l₀ ≫ f = h := pullback.lift_snd _ _ _
  have h₁ : l₁ ≫ f = h := pullback.lift_snd _ _ _
  obtain ⟨e⟩ := relativeFunctorIso_of_faithful_nerve_readout p r s hs f h i hi ei
    l₀ l₁ h₀ h₁ hv
  let M := relativeFunctorIsPullbackIso (IsPullback.of_hasPullback q δ) h (h ≫ δ) rfl
  have eh := e.map M.hom
  dsimp only [M] at eh
  rw [relativeFunctorIsPullbackIso_vertex, relativeFunctorIsPullbackIso_vertex] at eh
  simpa only [l₀, l₁, pullback.lift_fst] using (⟨eh⟩ : Nonempty _)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
