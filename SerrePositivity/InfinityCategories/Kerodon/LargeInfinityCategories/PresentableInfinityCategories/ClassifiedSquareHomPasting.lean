module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ClassifiedSquareLiftPasting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChangePasting

/-!
概要：元の実正方形の分類は、指定底変換の貼り合わせを介して合成を保つ。
方針：同じ引き戻しの持ち上げの合成を分類し、元の指定底変換の合成則を使う。
規約：実正方形とその分類射を選び直さない。
使われ方：Kerodon §5.6（Tag 027M）の指定Yoneda単位の始点固定の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open Project.QuasicategoryAuxiliaries
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

attribute [local instance] supplyClassifiedSquareHomNaturality_pullbackLeftFibration

private lemma isoPrecomp_hom {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (k : D ⟶ A) :
    (e.precomp k).hom = precomposeFunctorHom k e.hom := by
  rw [precomposeFunctorHom_eq_map]
  exact functorIso_precomp_hom e k

private lemma precomp_inv {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : FunctorIso f g) (k : D ⟶ A) :
    precomposeFunctorHom k e.inv = (e.precomp k).inv := by
  simpa only [Iso.symm_hom, functorIso_precomp_symm] using (isoPrecomp_hom e.symm k).symm

private lemma classifiedHom_map_eq {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    {f g : E ⟶ H} (hf : f ≫ q = p) (hg : g ≫ q = p) (h : f = g) :
    leftClassificationHom p q f hf = leftClassificationHom p q g hg := by
  cases h
  rfl

private lemma normalized_inverse_comp_heq {A X : SSet.{u}}
    {f g f' h : A ⟶ X} (hf : f = f') (e : FunctorIso f g) (w : FunctorHom h g) :
    HEq (w ≫ (diagramIsoCongr hf rfl e).inv) (w ≫ e.inv) := by
  subst f'
  simpa only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm,
    Iso.refl_trans, Iso.trans_refl] using (HEq.refl (w ≫ e.inv))

private lemma squarePastingAlgebra {L : Type v} [Category.{w} L]
    {X Y Z W V Q T : L} (u : X ⟶ Y) (bq : Z ≅ Y) (v : Z ⟶ W)
    (s : Y ⟶ V) (bn : W ≅ V) (B₀ : T ≅ W) (w : X ⟶ Q) (a' : Q ⟶ V) (N : T ≅ Q)
    (hv : bq.inv ≫ v = s ≫ bn.inv) (huv : u ≫ s = w ≫ a')
    (hpi : a' ≫ bn.inv ≫ B₀.inv = N.inv) :
    (u ≫ bq.inv) ≫ (v ≫ B₀.inv) = w ≫ N.inv := by
  calc
    (u ≫ bq.inv) ≫ (v ≫ B₀.inv) = u ≫ ((bq.inv ≫ v) ≫ B₀.inv) := by
      simp only [Category.assoc]
    _ = u ≫ ((s ≫ bn.inv) ≫ B₀.inv) := by rw [hv]
    _ = (u ≫ s) ≫ bn.inv ≫ B₀.inv := by simp only [Category.assoc]
    _ = (w ≫ a') ≫ bn.inv ≫ B₀.inv := by rw [huv]
    _ = w ≫ N.inv := by rw [Category.assoc, hpi]

private lemma precomp_comp_inv {A D X : SSet.{u}} {f g h : A ⟶ X}
    (k : D ⟶ A) (α : FunctorHom f g) (e : FunctorIso h g) :
    precomposeFunctorHom k (α ≫ e.inv) = precomposeFunctorHom k α ≫ (e.precomp k).inv := by
  rw [precomposeFunctorHom_comp, precomp_inv]

private lemma squarePastingNormalizedAlgebra {A B X : SSet.{u}} (k : A ⟶ B)
    {V T H : B ⟶ X} {P Q R S : A ⟶ X}
    (u : FunctorHom P Q) (bq : FunctorIso (k ≫ V) Q)
    (v : FunctorHom V H) (e : FunctorIso T H)
    (s : FunctorHom Q R) (bn : FunctorIso (k ≫ H) R)
    (w : FunctorHom P S) (a' : FunctorHom S R) (N : FunctorIso (k ≫ T) S)
    (hv : bq.inv ≫ precomposeFunctorHom k v = s ≫ bn.inv)
    (huv : u ≫ s = w ≫ a')
    (hpi : a' ≫ bn.inv ≫ (e.precomp k).inv = N.inv) :
    (u ≫ bq.inv) ≫ precomposeFunctorHom k (v ≫ e.inv) = w ≫ N.inv := by
  rw [precomp_comp_inv]
  exact squarePastingAlgebra u bq (precomposeFunctorHom k v) s bn
    (e.precomp k) w a' N hv huv hpi

private lemma squareNaturalityInverse {L : Type v} [Category.{w} L]
    {Z Y W V : L} (bq : Z ≅ Y) (bn : W ≅ V) (v : Z ⟶ W) (s : Y ⟶ V)
    (h : v ≫ bn.hom = bq.hom ≫ s) : bq.inv ≫ v = s ≫ bn.inv := by
  apply (cancel_mono bn.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

private lemma inverseThree {L : Type v} [Category.{w} L]
    {T W V Q : L} (B₀ : T ≅ W) (bn : W ≅ V) (a : V ⟶ Q) [IsIso a]
    (N : T ≅ Q) (a' : Q ⟶ V) (ha : a ≫ a' = 𝟙 _)
    (h : B₀ ≪≫ bn ≪≫ asIso a = N) : a' ≫ bn.inv ≫ B₀.inv = N.inv := by
  have hi := congrArg Iso.inv h
  have he : (asIso a).inv = a' := IsIso.inv_eq_of_hom_inv_id ha
  simpa only [Iso.trans_inv, Category.assoc, he] using hi

private def squareLiftClassify {A B E H : SSet.{u}} [Quasicategory A]
    (p : E ⟶ A) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (k : A ⟶ B) (f : E ⟶ H) (hf : f ≫ q = p ≫ k) :
    FunctorHom (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram (pullback.snd q k)) :=
  leftClassificationHom p (pullback.snd q k) (pullback.lift f p hf) (pullback.lift_snd _ _ _)

private def baseChangedSquareLiftClassify {A B C H J : SSet.{u}} [Quasicategory A]
    (q : H ⟶ B) (r : J ⟶ C) [LeftFibration q] [LeftFibration r]
    (l : B ⟶ C) (g : H ⟶ J) (hg : g ≫ r = q ≫ l) (k : A ⟶ B) :
    FunctorHom (leftStraighteningInfinityDiagram (pullback.snd q k))
      (leftStraighteningInfinityDiagram (pullback.snd (pullback.snd r l) k)) :=
  leftClassificationHom (pullback.snd q k) (pullback.snd (pullback.snd r l) k)
    (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange q (pullback.snd r l)
      (pullback.lift g q hg) (pullback.lift_snd _ _ _) k)
    (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection _ _ _ _ _)

private lemma classifiedSquareLift_pasting {A B C E H J : SSet.{u}}
    [Quasicategory A] (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k) (g : H ⟶ J) (hg : g ≫ r = q ≫ l) :
    leftClassificationHom p (pullback.snd q k) (pullback.lift f p hf) (pullback.lift_snd _ _ _) ≫
      leftClassificationHom (pullback.snd q k) (pullback.snd (pullback.snd r l) k)
        (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange
          q (pullback.snd r l) (pullback.lift g q hg) (pullback.lift_snd _ _ _) k)
        (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection _ _ _ _ _) =
    leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      leftClassificationHom (pullback.snd r (k ≫ l)) (pullback.snd (pullback.snd r l) k)
        (pullbackLeftPullbackSndIso r l k).inv (pullbackLeftPullbackSndIso_inv_snd_snd r l k) := by
  rw [leftClassificationHom_comp, leftClassificationHom_comp]
  apply classifiedHom_map_eq
  exact squareLift_pasting p q r k l f hf g hg

private lemma squarePastingInverse {A B C J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (r : J ⟶ C) [LeftFibration r] (k : A ⟶ B) (l : B ⟶ C) :
    leftClassificationHom (pullback.snd r (k ≫ l)) (pullback.snd (pullback.snd r l) k)
        (pullbackLeftPullbackSndIso r l k).inv (pullbackLeftPullbackSndIso_inv_snd_snd r l k) ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k).inv ≫
      ((leftStraighteningInfinityDiagram_baseChangeIso r l).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map k)).inv =
    (diagramIsoCongr
      (f' := (SSet.uliftFunctor.{u + 1, u}).map k ≫
        ((SSet.uliftFunctor.{u + 1, u}).map l ≫ leftStraighteningInfinityDiagram r))
      (by rw [Functor.map_comp, Category.assoc]) rfl
      (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))).inv := by
  let e := pullbackLeftPullbackSndIso r l k
  let a := leftClassificationHom (pullback.snd (pullback.snd r l) k)
    (pullback.snd r (k ≫ l)) e.hom (pullbackLeftPullbackSndIso_hom_snd r l k)
  let a' := leftClassificationHom (pullback.snd r (k ≫ l))
    (pullback.snd (pullback.snd r l) k) e.inv (pullbackLeftPullbackSndIso_inv_snd_snd r l k)
  letI := leftClassificationHom_preserves_iso (pullback.snd (pullback.snd r l) k)
    (pullback.snd r (k ≫ l)) e (pullbackLeftPullbackSndIso_hom_snd r l k)
    (pullbackLeftPullbackSndIso_inv_snd_snd r l k)
  have haa : a ≫ a' = 𝟙 _ := leftClassificationHom_iso_hom_inv
    (pullback.snd (pullback.snd r l) k) (pullback.snd r (k ≫ l)) e
    (pullbackLeftPullbackSndIso_hom_snd r l k) (pullbackLeftPullbackSndIso_inv_snd_snd r l k)
  have hi := leftStraightening_baseChange_pasting_iso r l k
  dsimp only at hi
  exact inverseThree _ _ a _ a' haa hi

private lemma squareLiftNaturalityInverse {A B C H J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (q : H ⟶ B) (r : J ⟶ C) [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C) (g : H ⟶ J) (hg : g ≫ r = q ≫ l) :
    (leftStraighteningInfinityDiagram_baseChangeIso q k).inv ≫
      precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (squareLiftClassify q r l g hg) =
    baseChangedSquareLiftClassify q r l g hg k ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k).inv := by
  have hn := leftClassificationHom_baseChange q (pullback.snd r l)
    (pullback.lift g q hg) (pullback.lift_snd _ _ _) k
  exact squareNaturalityInverse _ _ _ _ hn

private lemma squarePasting_of_laws {A B C E H J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l)
    (hv0 : (leftStraighteningInfinityDiagram_baseChangeIso q k).inv ≫
      precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (squareLiftClassify q r l g hg) =
    baseChangedSquareLiftClassify q r l g hg k ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k).inv)
    (huv0 : leftClassificationHom p (pullback.snd q k) (pullback.lift f p hf) (pullback.lift_snd _ _ _) ≫
      leftClassificationHom (pullback.snd q k) (pullback.snd (pullback.snd r l) k)
        (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange
          q (pullback.snd r l) (pullback.lift g q hg) (pullback.lift_snd _ _ _) k)
        (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection _ _ _ _ _) =
    leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      leftClassificationHom (pullback.snd r (k ≫ l)) (pullback.snd (pullback.snd r l) k)
        (pullbackLeftPullbackSndIso r l k).inv (pullbackLeftPullbackSndIso_inv_snd_snd r l k))
    (hpi0 : leftClassificationHom (pullback.snd r (k ≫ l)) (pullback.snd (pullback.snd r l) k)
        (pullbackLeftPullbackSndIso r l k).inv (pullbackLeftPullbackSndIso_inv_snd_snd r l k) ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k).inv ≫
      ((leftStraighteningInfinityDiagram_baseChangeIso r l).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map k)).inv =
    (diagramIsoCongr
      (f' := (SSet.uliftFunctor.{u + 1, u}).map k ≫
        ((SSet.uliftFunctor.{u + 1, u}).map l ≫ leftStraighteningInfinityDiagram r))
      (by rw [Functor.map_comp, Category.assoc]) rfl
      (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))).inv) :
    leftClassificationSquareHom p q k f hf ≫
        precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
          (leftClassificationSquareHom q r l g hg) =
      leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p
          (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      (diagramIsoCongr
        (f' := (SSet.uliftFunctor.{u + 1, u}).map k ≫
          ((SSet.uliftFunctor.{u + 1, u}).map l ≫ leftStraighteningInfinityDiagram r))
        (by rw [Functor.map_comp, Category.assoc]) rfl
        (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))).inv := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let u := squareLiftClassify p q k f hf
  let v := squareLiftClassify q r l g hg
  let w := squareLiftClassify p r (k ≫ l) (f ≫ g)
    (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc])
  let s := baseChangedSquareLiftClassify q r l g hg k
  let a' := leftClassificationHom (pullback.snd r (k ≫ l))
    (pullback.snd (pullback.snd r l) k) (pullbackLeftPullbackSndIso r l k).inv
    (pullbackLeftPullbackSndIso_inv_snd_snd r l k)
  let bq := leftStraighteningInfinityDiagram_baseChangeIso q k
  let bl := leftStraighteningInfinityDiagram_baseChangeIso r l
  let bn := leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k
  let bd := leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l)
  have hc : U.map (k ≫ l) ≫ leftStraighteningInfinityDiagram r =
      U.map k ≫ (U.map l ≫ leftStraighteningInfinityDiagram r) := by
    rw [Functor.map_comp, Category.assoc]
  let N := diagramIsoCongr hc rfl bd
  have hv : bq.inv ≫ precomposeFunctorHom (U.map k) v = s ≫ bn.inv :=
    hv0
  have huv : u ≫ s = w ≫ a' := huv0
  have hpi : a' ≫ bn.inv ≫ (bl.precomp (U.map k)).inv = N.inv := hpi0
  simp only [leftClassificationSquareHom.eq_def]
  change (u ≫ bq.inv) ≫ precomposeFunctorHom (U.map k) (v ≫ bl.inv) = w ≫ N.inv
  as_aux_lemma =>
    exact squarePastingNormalizedAlgebra (U.map k) u bq v bl s bn w a' N hv huv hpi


private lemma squarePasting_with_inverse {A B C E H J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l)
    (hv0 : (leftStraighteningInfinityDiagram_baseChangeIso q k).inv ≫
      precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (squareLiftClassify q r l g hg) =
    baseChangedSquareLiftClassify q r l g hg k ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k).inv)
    (huv0 : leftClassificationHom p (pullback.snd q k) (pullback.lift f p hf) (pullback.lift_snd _ _ _) ≫
      leftClassificationHom (pullback.snd q k) (pullback.snd (pullback.snd r l) k)
        (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange
          q (pullback.snd r l) (pullback.lift g q hg) (pullback.lift_snd _ _ _) k)
        (F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange_projection _ _ _ _ _) =
    leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      leftClassificationHom (pullback.snd r (k ≫ l)) (pullback.snd (pullback.snd r l) k)
        (pullbackLeftPullbackSndIso r l k).inv (pullbackLeftPullbackSndIso_inv_snd_snd r l k)) :
    leftClassificationSquareHom p q k f hf ≫
        precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
          (leftClassificationSquareHom q r l g hg) =
      leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p
          (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      (diagramIsoCongr
        (f' := (SSet.uliftFunctor.{u + 1, u}).map k ≫
          ((SSet.uliftFunctor.{u + 1, u}).map l ≫ leftStraighteningInfinityDiagram r))
        (by rw [Functor.map_comp, Category.assoc]) rfl
        (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))).inv :=
  squarePasting_of_laws p q r k l f hf g hg hv0 huv0 (squarePastingInverse r k l)

private lemma squarePasting_with_composition {A B C E H J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l)
    (hv0 : (leftStraighteningInfinityDiagram_baseChangeIso q k).inv ≫
      precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
        (squareLiftClassify q r l g hg) =
    baseChangedSquareLiftClassify q r l g hg k ≫
      (leftStraighteningInfinityDiagram_baseChangeIso (pullback.snd r l) k).inv) :
    leftClassificationSquareHom p q k f hf ≫
        precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
          (leftClassificationSquareHom q r l g hg) =
      leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p
          (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      (diagramIsoCongr
        (f' := (SSet.uliftFunctor.{u + 1, u}).map k ≫
          ((SSet.uliftFunctor.{u + 1, u}).map l ≫ leftStraighteningInfinityDiagram r))
        (by rw [Functor.map_comp, Category.assoc]) rfl
        (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))).inv :=
  squarePasting_with_inverse p q r k l f hf g hg hv0
    (classifiedSquareLift_pasting p q r k l f hf g hg)

private lemma squarePasting_normalized {A B C E H J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l) :
    leftClassificationSquareHom p q k f hf ≫
        precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
          (leftClassificationSquareHom q r l g hg) =
      leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p
          (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _) ≫
      (diagramIsoCongr
        (f' := (SSet.uliftFunctor.{u + 1, u}).map k ≫
          ((SSet.uliftFunctor.{u + 1, u}).map l ≫ leftStraighteningInfinityDiagram r))
        (by rw [Functor.map_comp, Category.assoc]) rfl
        (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))).inv :=
  squarePasting_with_composition p q r k l f hf g hg (squareLiftNaturalityInverse q r k l g hg)

/-- 概要：二つの実正方形を分類した射の合成は、合成正方形の元の分類射。
方針：持ち上げの合成を分類し、同じ指定底変換の自然性と貼り合わせを相殺する。
規約：全図式の元の射の異種等式。使われ方：同じ指定Yoneda単位の始点固定の同定。 -/
lemma leftClassificationSquareHom_pasting {A B C E H J : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l) :
    HEq (leftClassificationSquareHom p q k f hf ≫
        precomposeFunctorHom ((SSet.uliftFunctor.{u + 1, u}).map k)
          (leftClassificationSquareHom q r l g hg))
      (leftClassificationSquareHom p r (k ≫ l) (f ≫ g)
        (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc])) := by
  exact (squarePasting_normalized p q r k l f hf g hg).heq.trans
    (normalized_inverse_comp_heq
      (by rw [Functor.map_comp, Category.assoc])
      (leftStraighteningInfinityDiagram_baseChangeIso r (k ≫ l))
      (leftClassificationHom p (pullback.snd r (k ≫ l))
        (pullback.lift (f ≫ g) p
          (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]))
        (pullback.lift_snd _ _ _)))

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
