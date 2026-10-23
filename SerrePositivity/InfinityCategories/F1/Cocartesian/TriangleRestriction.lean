module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TriangleCone

/-!
概要：後半の辺が cocartesian な三角形から最初の辺への相対 coslice 制限。
方針：三角形の錐の延長を curry して全境界の充填に移す。
規約：inner fibration 性と後半の辺の cocartesian 性だけを仮定する。
使われ方：Kerodon Corollary 5.1.2.4、Proposition 5.2.5.1 の合成性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：後半の辺が cocartesian なら最初の辺への相対制限は任意の部分複体を持ち上げる。
方針：制限先の二つの錐を取り出して三角形の錐に延長する。
規約：A₀ は任意の部分複体。
使われ方：Kerodon Corollary 5.1.2.4、合成辺を判定する比較写像の充填。 -/
lemma relativeCosliceRestriction_triangleFirstEdge_lift {X Y A : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t)))
    (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (relativeCosliceRestriction t q (stdSimplex.δ (2 : Fin 3))) := by
  let f := (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2])
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
  obtain ⟨T, hT, hTb, hTf, hTq⟩ := cocartesianTriangle_extendCone t q he A₀ G H B
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

/-- 概要：後半の辺が cocartesian な三角形から最初の辺への相対制限は trivial Kan fibration。
方針：全境界の持ち上げ性で判定する。
規約：最初の辺の cocartesian 性はここでは不要。
使われ方：Kerodon Corollary 5.1.2.4、始点への相対制限の合成。 -/
lemma relativeCosliceRestriction_triangleFirstEdge {X Y : SSet.{u}}
    (t : (Δ[2] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (he : IsCocartesianEdge q (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ t))) :
    TrivialKanFibration (relativeCosliceRestriction t q (stdSimplex.δ (2 : Fin 3))) :=
  (trivialKanFibration_iff_boundary _).2
    (fun n ↦ relativeCosliceRestriction_triangleFirstEdge_lift t q he (boundary n))

end SerrePositivity.InfinityCategories
