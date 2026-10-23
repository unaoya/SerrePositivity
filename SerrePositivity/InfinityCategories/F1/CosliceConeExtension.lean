module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SourceRestriction

/-!
概要：相対 coslice 制限の充填性を錐の厳密な延長として使う。
方針：錐を curry して比較写像の持ち上げを取り、uncurry で三つの条件に戻す。
規約：部分パラメーターの錐、部分図式の錐、底の錐を同時に固定する。
使われ方：Kerodon Proposition 5.2.5.1、合成の三角形の錐の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対制限が trivial Kan fibration なら三つの指定を保つ錐の延長が存在。
方針：錐の指定を可換四角形の比較写像の持ち上げに移す。
規約：A₀ は任意の部分複体、f は任意の図式の射。
使われ方：Kerodon Proposition 5.2.5.1、後半の辺の錐を持ち上げる。 -/
lemma relativeCosliceRestriction_extendCone {K L X Y A : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) (f : L ⟶ K)
    [TrivialKanFibration (relativeCosliceRestriction p q f)] (A₀ : A.Subcomplex)
    (G : join K (A₀ : SSet.{u}) ⟶ X) (H : join L A ⟶ X) (B : join K A ⟶ Y)
    (hG : joinInl K (A₀ : SSet.{u}) ≫ G = p)
    (hH : joinInl L A ≫ H = f ≫ p) (hB : joinInl K A ≫ B = p ≫ q)
    (hGH : joinMap f (𝟙 (A₀ : SSet.{u})) ≫ G = joinMap (𝟙 L) A₀.ι ≫ H)
    (hGq : G ≫ q = joinMap (𝟙 K) A₀.ι ≫ B)
    (hHq : H ≫ q = joinMap f (𝟙 A) ≫ B) :
    ∃ T : join K A ⟶ X, joinInl K A ≫ T = p ∧
      joinMap (𝟙 K) A₀.ι ≫ T = G ∧ joinMap f (𝟙 A) ≫ T = H ∧ T ≫ q = B := by
  let a := sliceUnderCurry G hG
  let b := sliceUnderCurry H hH
  let c := sliceUnderCurry B hB
  have hab : a ≫ sliceUnderRestrict p f = A₀.ι ≫ b := by
    apply sliceUnderUncurry_injective (f ≫ p)
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp]
    simpa only [a, b, sliceUnderUncurry_curry] using hGH
  have hac : a ≫ sliceUnderPostcomp p q = A₀.ι ≫ c := by
    apply sliceUnderUncurry_injective (p ≫ q)
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp]
    simpa only [a, c, sliceUnderUncurry_curry] using hGq
  have hbc : b ≫ sliceUnderPostcomp (f ≫ p) q = c ≫ sliceUnderRestrict (p ≫ q) f := by
    apply sliceUnderUncurry_injective ((f ≫ p) ≫ q)
    simpa only [b, c, sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict,
      sliceUnderUncurry_curry] using hHq
  have : TrivialKanFibration (squareComparison (cosliceRestrictionSquare p q f)) :=
    (inferInstance : TrivialKanFibration (relativeCosliceRestriction p q f))
  obtain ⟨l, hl, hlf, hlq⟩ := squareComparison_exists_lift
    (cosliceRestrictionSquare p q f) A₀.ι a b c hab hac hbc
  refine ⟨sliceUnderUncurry l, sliceUnderUncurry_fixed l, ?_, ?_, ?_⟩
  · have h := congrArg sliceUnderUncurry hl
    simpa only [a, sliceUnderUncurry_precomp, sliceUnderUncurry_curry] using h
  · have h := congrArg sliceUnderUncurry hlf
    simpa only [b, sliceUnderUncurry_restrict, sliceUnderUncurry_curry] using h
  · have h := congrArg sliceUnderUncurry hlq
    simpa only [c, sliceUnderUncurry_postcomp, sliceUnderUncurry_curry] using h

end SerrePositivity.InfinityCategories
