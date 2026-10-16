module
public import SerrePositivity.DifferentialGraded.Complexes.ExactColimits
public import SerrePositivity.HomologicalAlgebra.StupidTruncation
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-! # 下からのstupid truncationの可算列と網羅的余極限 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 下端を小さくする包含の各次数の成分。 -/
def lowerTruncationMapComponent (K : Complex A) (a b : ℤ) (hab : b ≤ a) (q : ℤ) :
    (StupidTruncation.above K a).X q ⟶ (StupidTruncation.above K b).X q :=
  if hq : a ≤ q then
    (StupidTruncation.aboveXIso K a q hq).hom ≫
      (StupidTruncation.aboveXIso K b q (hab.trans hq)).inv
  else 0

lemma lowerTruncationMapComponent_inclusion (K : Complex A) (a b : ℤ) (hab : b ≤ a) (q : ℤ) :
    lowerTruncationMapComponent A K a b hab q ≫ (StupidTruncation.inclusion K b).f q =
      (StupidTruncation.inclusion K a).f q := by
  by_cases hq : a ≤ q
  · simp only [lowerTruncationMapComponent, dite_eq_left hq,
      StupidTruncation.inclusion_f K b q (hab.trans hq),
      StupidTruncation.inclusion_f K a q hq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (StupidTruncation.above_isZero_X K a q (by omega)).eq_of_src _ _

/-- 下端b≤aなら、a以上の切り詰めはb以上の切り詰めへ含まれる。 -/
def lowerTruncationMap (K : Complex A) (a b : ℤ) (hab : b ≤ a) :
    StupidTruncation.above K a ⟶ StupidTruncation.above K b where
  f q := lowerTruncationMapComponent A K a b hab q
  comm' i j _ := by
    apply (cancel_mono ((StupidTruncation.inclusion K b).f j)).1
    rw [Category.assoc, ← (StupidTruncation.inclusion K b).comm,
      ← Category.assoc, lowerTruncationMapComponent_inclusion, Category.assoc,
      lowerTruncationMapComponent_inclusion, (StupidTruncation.inclusion K a).comm]

@[reassoc]
lemma lowerTruncationMap_inclusion (K : Complex A) (a b : ℤ) (hab : b ≤ a) :
    lowerTruncationMap A K a b hab ≫ StupidTruncation.inclusion K b =
      StupidTruncation.inclusion K a := by
  apply Hom.ext
  funext q
  exact lowerTruncationMapComponent_inclusion A K a b hab q

lemma lowerTruncationMap_id (K : Complex A) (a : ℤ) :
    lowerTruncationMap A K a a le_rfl = 𝟙 _ := by
  apply Hom.ext
  funext q
  apply (cancel_mono ((StupidTruncation.inclusion K a).f q)).1
  simpa only [comp_f, id_f, Category.id_comp] using
    congrArg (fun f => f.f q) (lowerTruncationMap_inclusion A K a a le_rfl)

lemma lowerTruncationMap_comp (K : Complex A) (a b c : ℤ) (hab : b ≤ a) (hbc : c ≤ b) :
    lowerTruncationMap A K a b hab ≫ lowerTruncationMap A K b c hbc =
      lowerTruncationMap A K a c (hbc.trans hab) := by
  apply Hom.ext
  funext q
  apply (cancel_mono ((StupidTruncation.inclusion K c).f q)).1
  change (lowerTruncationMap A K a b hab).f q ≫
      (lowerTruncationMap A K b c hbc).f q ≫ (StupidTruncation.inclusion K c).f q = _
  simp only [lowerTruncationMap, lowerTruncationMapComponent_inclusion]

/-- 切り詰め下端を0,−1,−2,…とする可算図式。 -/
def lowerTruncationSequence (K : Complex A) : ℕ ⥤ Complex A where
  obj n := StupidTruncation.above K (-(n : ℤ))
  map {i j} f := lowerTruncationMap A K (-(i : ℤ)) (-(j : ℤ))
    (by have := leOfHom f; omega)
  map_id n := lowerTruncationMap_id A K _
  map_comp f g := (lowerTruncationMap_comp A K _ _ _ _ _).symm

/-- 元の非有界複体への包含の余錐。 -/
def lowerTruncationCocone (K : Complex A) : Cocone (lowerTruncationSequence A K) where
  pt := K
  ι := { app := fun n => StupidTruncation.inclusion K (-(n : ℤ))
         naturality := fun i j f => by
           change lowerTruncationMap A K (-(i : ℤ)) (-(j : ℤ)) _ ≫
             StupidTruncation.inclusion K (-(j : ℤ)) =
               StupidTruncation.inclusion K (-(i : ℤ)) ≫ 𝟙 K
           rw [lowerTruncationMap_inclusion, Category.comp_id] }

/-- 各次数でやがて同型となる包含から、非有界複体を余極限として回復する。 -/
def lowerTruncationCoconeIsColimit (K : Complex A) :
    IsColimit (lowerTruncationCocone A K) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  let F := lowerTruncationSequence A K ⋙ eval (ModuleCat.{u} A) (.up ℤ) q
  let c : Cocone F := (eval (ModuleCat.{u} A) (.up ℤ) q).mapCocone
    (lowerTruncationCocone A K)
  let N := (-q).toNat
  have hN : -(N : ℤ) ≤ q := by dsimp [N]; omega
  have : IsIso (c.ι.app N) := by
    change IsIso ((StupidTruncation.inclusion K (-(N : ℤ))).f q)
    exact StupidTruncation.inclusion_f_isIso K _ q hN
  have hF : F.IsEventuallyConstantFrom N := by
    intro j f
    have hj : -(j : ℤ) ≤ q := by have := leOfHom f; omega
    have : IsIso (c.ι.app j) := by
      change IsIso ((StupidTruncation.inclusion K (-(j : ℤ))).f q)
      exact StupidTruncation.inclusion_f_isIso K _ q hj
    have : IsIso (F.map f ≫ c.ι.app j) := by rw [c.w f]; infer_instance
    exact IsIso.of_isIso_comp_right (F.map f) (c.ι.app j)
  exact hF.isColimitOfIsIso c

/-- 下からの切り詰めの実際の余極限と元の複体との同型。 -/
def lowerTruncationColimitIso (K : Complex A) : colimit (lowerTruncationSequence A K) ≅ K :=
  (colimit.isColimit _).coconePointUniqueUpToIso (lowerTruncationCoconeIsColimit A K)

end SerrePositivity.DifferentialGraded
