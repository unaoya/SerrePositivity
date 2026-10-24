module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianTriangleMiddleCone

/-!
概要：最初の辺と長辺が cocartesian な三角形から真ん中の頂点への相対 coslice 制限。
方針：構成した余錐の延長を curry して全境界の充填に移す。
規約：inner fibration 性と二辺の cocartesian 性だけを仮定する。
使われ方：三角形の後半の辺の cocartesian 性の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最初の辺と長辺が cocartesian なら真ん中の頂点への相対制限は境界を持ち上げる。
方針：境界問題を余錐の相対延長へ移す。
規約：境界の全次元を扱う。
使われ方：相対制限の trivial Kan fibration 性の判定。 -/
lemma relativeCosliceRestriction_middle_boundary {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (hf : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hh : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))) (n : ℕ) :
    HasLiftingProperty (boundary n).ι (relativeCosliceRestriction t q
      (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))) := by
  let A := (Δ[n] : SSet.{u})
  let A₀ := boundary.{u} n
  let f := (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ stdSimplex.δ (2 : Fin 3)
  constructor
  intro a b sq
  let r := pullback.fst (sliceUnderPostcomp (f ≫ t) q) (sliceUnderRestrict (t ≫ q) f)
  let s := pullback.snd (sliceUnderPostcomp (f ≫ t) q) (sliceUnderRestrict (t ≫ q) f)
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry (b ≫ r)
  let B := sliceUnderUncurry (b ≫ s)
  have ha : a ≫ sliceUnderRestrict t f = A₀.ι ≫ (b ≫ r) := by
    have h := congrArg (fun z ↦ z ≫ r) sq.w
    simpa only [r, f, relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_fst] using h
  have hb : a ≫ sliceUnderPostcomp t q = A₀.ι ≫ (b ≫ s) := by
    have h := congrArg (fun z ↦ z ≫ s) sq.w
    simpa only [s, f, relativeCosliceRestriction, squareComparison, Category.assoc,
      pullback.lift_snd] using h
  have hGH : joinMap f (𝟙 (A₀ : SSet.{u})) ≫ G = joinMap (𝟙 _) A₀.ι ≫ H := by
    have h := congrArg sliceUnderUncurry ha
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at h
    exact h
  have hGq : G ≫ q = joinMap (𝟙 _) A₀.ι ≫ B := by
    have h := congrArg sliceUnderUncurry hb
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at h
    exact h
  have hHq : H ≫ q = joinMap f (𝟙 A) ≫ B := by
    have h : (b ≫ r) ≫ sliceUnderPostcomp (f ≫ t) q =
        (b ≫ s) ≫ sliceUnderRestrict (t ≫ q) f := by
      simpa only [r, s, Category.assoc] using congrArg (fun z ↦ b ≫ z)
        (pullback.condition (f := sliceUnderPostcomp (f ≫ t) q)
          (g := sliceUnderRestrict (t ≫ q) f))
    have hh := congrArg sliceUnderUncurry h
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict] at hh
    exact hh
  obtain ⟨T, hT, hTb, hTf, hTq⟩ := SerrePositivity.InfinityCategories.cocartesianTriangle_extendConeFromMiddle t q hf hh n G H B
    (sliceUnderUncurry_fixed a) (sliceUnderUncurry_fixed (b ≫ r))
    (sliceUnderUncurry_fixed (b ≫ s)) hGH hGq hHq
  refine CommSq.HasLift.mk' { l := sliceUnderCurry T hT, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective t
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hTb
  · apply pullback.hom_ext
    · change sliceUnderCurry T hT ≫ relativeCosliceRestriction t q f ≫ r = b ≫ r
      have hr : relativeCosliceRestriction t q f ≫ r = sliceUnderRestrict t f :=
        pullback.lift_fst _ _ _
      rw [hr]
      apply sliceUnderUncurry_injective (f ≫ t)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
      exact hTf
    · change sliceUnderCurry T hT ≫ relativeCosliceRestriction t q f ≫ s = b ≫ s
      have hs : relativeCosliceRestriction t q f ≫ s = sliceUnderPostcomp t q :=
        pullback.lift_snd _ _ _
      rw [hs]
      apply sliceUnderUncurry_injective (t ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hTq

/-- 概要：最初と長い辺が cocartesian な三角形の真ん中の頂点への相対制限は trivial Kan fibration。
方針：全境界の持ち上げ性で判定する。
規約：全空間と底の quasicategory 性は不要。
使われ方：後半の辺の cocartesian 性の消去の入力。 -/
lemma relativeCosliceRestriction_middle {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (hf : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ t)))
    (hh : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ t))) :
    TrivialKanFibration (relativeCosliceRestriction t q
      (stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))) :=
  (trivialKanFibration_iff_boundary _).2
    (relativeCosliceRestriction_middle_boundary t q hf hh)

end SerrePositivity.InfinityCategories
