module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedSimplex
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedCoordinateNaturality
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleLabelBaselineRealization

/-!
概要：実際の再構成単体は、元の全パラメーターの面・退化を保つ。
方針：基準単体の自然性を保持し、変更した長 Hom だけを座標の自然性で照合する。
規約：元の小さい豊穣 Hom と大きいパラメーターを同じ全族として扱う。
使われ方：再構成単体を一つの全族の射へ束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

private lemma triangleFunctor_map_congr
    {D : Type w} [EnrichedCategory SSet.{u} D]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} D C} (h : F = G) (i j : D) :
    F.map i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (congrArg (fun T : EnrichedFunctor SSet.{u} D C => T.obj i) h)
      (congrArg (fun T : EnrichedFunctor SSet.{u} D C => T.obj j) h)) = G.map i j := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
  {K L : SSet.{max u v}}
  (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))

lemma triangleSeparatedBaseline_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : K _⦋n⦌) (t : Fin (n + 1) →o Fin 3) :
    (SimplicialNerve C).map α.op (triangleSeparatedBaseline f g s t) =
      triangleSeparatedBaseline f g (K.map α.op s) (t.comp α.toOrderHom) := by
  have hf : (SimplicialCategory.sHom X Y).map α.op (f.app (Opposite.op ⦋n⦌) s).down =
      (f.app (Opposite.op ⦋m⦌) (K.map α.op s)).down :=
    by
      have h := ConcreteCategory.congr_hom (f.naturality α.op) s
      exact (congrArg (fun x : ((SSet.uliftFunctor.{v, u}).obj
        (SimplicialCategory.sHom X Y)) _⦋m⦌ => x.down) h).symm
  have hg : (SimplicialCategory.sHom Y Z).map α.op (g.app (Opposite.op ⦋n⦌) s).down =
      (g.app (Opposite.op ⦋m⦌) (K.map α.op s)).down :=
    by
      have h := ConcreteCategory.congr_hom (g.naturality α.op) s
      exact (congrArg (fun x : ((SSet.uliftFunctor.{v, u}).obj
        (SimplicialCategory.sHom Y Z)) _⦋m⦌ => x.down) h).symm
  change (SimplicialNerve C).map α.op (triangleLabelBaseline _ _ t) =
    triangleLabelBaseline _ _ (t.comp α.toOrderHom)
  rw [triangleLabelBaseline_naturality, hf, hg]

lemma triangleSeparatedLongHom_naturality
    (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (s : K _⦋n⦌) (r : L _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i j : Fin (m + 1)) (hi : t (α.toOrderHom i) = 0) :
    thickeningDirectHom α i j ≫ triangleSeparatedLongHom M s r t hi (α.toOrderHom j) =
      triangleSeparatedLongHom M (K.map α.op s) (L.map α.op r) (t.comp α.toOrderHom) hi j := by
  apply (SSet.uliftFunctor.{v, u}).map_injective
  rw [Functor.map_comp, triangleSeparatedLongHom_map_coordinates,
    triangleSeparatedLongHom_map_coordinates, ← Category.assoc,
    triangleSeparatedCoordinateMap_naturality]

variable (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
  (hM : prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (K ⊗ K) L ≫ CartesianMonoidalCategory.fst K K ≫ f)
      (CartesianMonoidalCategory.fst (K ⊗ K) L ≫ CartesianMonoidalCategory.snd K K ≫ g) ≫
    (HomotopyLimits.uliftTensorIso.{u, v}
      (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))

lemma triangleSeparatedSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3) :
    (SimplicialNerve C).map α.op (triangleSeparatedSimplex f g M hM s r t) =
      triangleSeparatedSimplex f g M hM (K.map α.op s) (L.map α.op r)
        (t.comp α.toOrderHom) := by
  have hb := triangleSeparatedBaseline_naturality f g α s t
  let ho (i : Fin (m + 1)) := congrArg (fun T : (SimplicialNerve C) _⦋m⦌ =>
    T.obj ⟨ULift.up i⟩) hb
  apply EnrichedFunctor.ext SSet (fun i => ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change thickeningDirectHom α i j ≫
      triangleSeparatedAssignedHom f g M s r t (α.toOrderHom i) (α.toOrderHom j) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (ho i) (ho j)) =
    triangleSeparatedAssignedHom f g M (K.map α.op s) (L.map α.op r) (t.comp α.toOrderHom) i j
  by_cases hi : t (α.toOrderHom i) = 0
  · by_cases hj : t (α.toOrderHom j) = 2
    · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleSeparatedBaseline_obj_zero f g (K.map α.op s) (t.comp α.toOrderHom) i hi)
        (triangleSeparatedBaseline_obj_two f g (K.map α.op s) (t.comp α.toOrderHom) j hj)))).1
      simp only [Category.assoc, eqToHom_trans]
      rw [triangleSeparatedAssignedHom_long f g M s r t _ _ hi hj,
        triangleSeparatedAssignedHom_long f g M (K.map α.op s) (L.map α.op r)
          (t.comp α.toOrderHom) i j hi hj]
      exact triangleSeparatedLongHom_naturality M α s r t i j hi
    · rw [triangleSeparatedAssignedHom, triangleSeparatedAssignedHom,
        triangleLabelReplacedHom_proper (triangleSeparatedBaseline f g s t) t
          (triangleSeparatedReplacementHom f g M s r t) _ _ (Or.inr hj),
        triangleLabelReplacedHom_proper
          (triangleSeparatedBaseline f g (K.map α.op s) (t.comp α.toOrderHom))
          (t.comp α.toOrderHom)
          (triangleSeparatedReplacementHom f g M (K.map α.op s) (L.map α.op r)
            (t.comp α.toOrderHom)) i j (Or.inr hj)]
      exact triangleFunctor_map_congr hb ⟨ULift.up i⟩ ⟨ULift.up j⟩
  · rw [triangleSeparatedAssignedHom, triangleSeparatedAssignedHom,
      triangleLabelReplacedHom_proper (triangleSeparatedBaseline f g s t) t
        (triangleSeparatedReplacementHom f g M s r t) _ _ (Or.inl hi),
      triangleLabelReplacedHom_proper
        (triangleSeparatedBaseline f g (K.map α.op s) (t.comp α.toOrderHom))
        (t.comp α.toOrderHom)
        (triangleSeparatedReplacementHom f g M (K.map α.op s) (L.map α.op r)
          (t.comp α.toOrderHom)) i j (Or.inl hi)]
    exact triangleFunctor_map_congr hb ⟨ULift.up i⟩ ⟨ULift.up j⟩

end SerrePositivity.InfinityCategories
