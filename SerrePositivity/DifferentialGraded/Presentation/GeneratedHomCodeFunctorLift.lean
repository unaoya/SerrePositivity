module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCodeFaithful
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomFunctorLift
public import SerrePositivity.DifferentialGraded.Functor.FullHomLift
/-!
概要：指定係数閉包に入る元の出発 dg 関手を固定基底の共通コードへ持ち上げる。
方針：実係数閉包への持ち上げを、コードの全 Hom 同型の逆で輸送する。
規約：元の対象ラベルと全 Hom 上の実評価の厳密な因子化を保持する。
使われ方：c′ の元の出発提示と任意閉射を同時に含む精密化の出発関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.InfinityCategories
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord

def codeToClosure :
    letI := category source target degree R D value coefficient
    DGFunctor R ((code R D κ a source target degree value coefficient hκ hI).Objects R κ)
      (Set.Iio a) := by
  letI := category source target degree R D value coefficient
  exact dgCategoryPresentationOfHomSurjectionsEvaluation R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI)

lemma codeToClosure_homIso
    (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ) :
    letI := category source target degree R D value coefficient
    IsIso ((codeToClosure R D κ a source target degree value coefficient hκ hI).map x y) := by
  letI := category source target degree R D value coefficient
  exact dgCategoryPresentationOfHomSurjectionsEvaluation_homIso R (Set.Iio a) κ a id
    (ordinalCover R D κ a source target degree value coefficient hκ hI)
    (ordinalCover_surjective R D κ a source target degree value coefficient hκ hI) x y

variable (C : Type w) [DGCategory R C] (F : DGFunctor R C (DGObjectImage value))
  (hF : ∀ x y n (f : GradedHom R x y n), (F.map x y).f n f ∈
    linearSpan source target degree R D value coefficient (F.obj x).label (F.obj y).label n)

def codeFunctorLift : DGFunctor R C
    ((code R D κ a source target degree value coefficient hκ hI).Objects R κ) := by
  letI := category source target degree R D value coefficient
  let G := liftFunctor source target degree R D value coefficient C F hF
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  exact dgFunctorFullHomLift R _ _ L
    (codeToClosure_homIso R D κ a source target degree value coefficient hκ hI) C
    (fun x => (F.obj x).label) G.map G.map_id G.map_comp

lemma codeFunctorLift_map (x y : C) :
    letI := category source target degree R D value coefficient
    (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).map x y ≫
      (codeToClosure R D κ a source target degree value coefficient hκ hI).map
        (F.obj x).label (F.obj y).label =
      liftHom source target degree R D value coefficient C F hF x y := by
  letI := category source target degree R D value coefficient
  exact dgFunctorFullHomLift_map R _ _
    (codeToClosure R D κ a source target degree value coefficient hκ hI)
    (codeToClosure_homIso R D κ a source target degree value coefficient hκ hI) C
    (fun x => (F.obj x).label)
    (liftFunctor source target degree R D value coefficient C F hF).map
    (liftFunctor source target degree R D value coefficient C F hF).map_id
    (liftFunctor source target degree R D value coefficient C F hF).map_comp x y

lemma codeFunctorLift_comp_evaluation :
    (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).comp
      (codeEvaluation R D κ a source target degree value coefficient hκ hI) =
      F.comp (dgObjectImageEvaluation R value) := by
  letI := category source target degree R D value coefficient
  apply EnrichedFunctor.ext (Complex R)
    (F := (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).comp
      (codeEvaluation R D κ a source target degree value coefficient hκ hI))
    (G := F.comp (dgObjectImageEvaluation R value)) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id]
  change (codeFunctorLift R D κ a source target degree value coefficient hκ hI C F hF).map x y ≫
    ((codeToClosure R D κ a source target degree value coefficient hκ hI).map
      (F.obj x).label (F.obj y).label ≫
      inclusion source target degree R D value coefficient (F.obj x).label (F.obj y).label) = F.map x y
  rw [← Category.assoc, codeFunctorLift_map, liftHom_inclusion]

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
