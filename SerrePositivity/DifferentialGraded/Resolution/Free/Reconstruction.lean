module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Category

/-! # 自由dg圏上のdg関手の生成辺からの再構成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]
  (E : Type w) [DGCategory A E]

lemma composition_edge_path (K : ComplexQuiver A D) (x b y : D) (w : List D) :
    (edgeInclusion A D K x b ⊗ₘ pathInclusion A D K b y (.inr w)) ≫
        composition A D K x b y = pathInclusion A D K x y (.inr (b :: w)) := by
  have h := composition_nonempty A D K x b y [] w
  exact h.trans (Category.id_comp _)

lemma functor_word (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E)
    (w : List D) (x y : D) :
    pathInclusion A D K x y (.inr w) ≫ F.map x y =
      wordEvaluation A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) w x y := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    have hc := F.map_comp x b y
    change composition A D K x b y ≫ F.map x y =
      (F.map x b ⊗ₘ F.map b y) ≫ eComp (Complex A) (F.obj x) (F.obj b) (F.obj y) at hc
    rw [← composition_edge_path A D K x b y w, Category.assoc, hc]
    rw [← Category.assoc, tensorHom_comp_tensorHom, ih]
    rfl

lemma functor_path (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E)
    {x y : D} (p : PathIndex D x y) :
    pathInclusion A D K x y p ≫ F.map x y =
      pathEvaluation A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) p := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    exact F.map_id x
  | inr w => exact functor_word A D E K F w x y

lemma homEvaluation_reconstruction (K : ComplexQuiver A D)
    (F : DGFunctor A (Objects A D K) E) (x y : D) :
    homEvaluation A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) x y =
      F.map x y := by
  apply homComplex_ext A D K x y
  intro p
  exact (pathInclusion_homEvaluation A D E K F.obj _ x y p).trans
    (functor_path A D E K F p).symm

lemma lift_reconstruction (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    lift A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) = F := by
  apply EnrichedFunctor.ext (Complex A)
    (F := lift A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y))
    (G := F) (fun _ => rfl)
  intro x y
  change homEvaluation A D E K F.obj _ x y ≫ eqToHom (by rfl) = F.map x y
  rw [eqToHom_refl, Category.comp_id]
  exact homEvaluation_reconstruction A D E K F x y

end SerrePositivity.DifferentialGraded.FreeDGCategory
