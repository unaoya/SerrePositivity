module
public import SerrePositivity.KST.Comparison.FibrantPullbackMap

/-! # 二方向の厳密な基底変換の可換性
概要：基底上の射の引き戻しと基底変換射の合成は厳密に可換。
方針：二つの pullback 射影を計算する。
規約：Kan 性は不要。使われ方：局所化同型の検出を基底の分解に沿って移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.KST.Comparison

/-- 基底上の射の変換と基底変換射は元の厳密な引き戻しで可換。 -/
lemma pullbackMapBase_slice_naturality {E E' B : SSet.{u}}
    (t : E ⟶ B) (t' : E' ⟶ B) (a : E ⟶ E') (ha : a ≫ t' = t)
    {X Y : Over B} (f : X ⟶ Y) :
    (sliceFiberFunctor t).map f ≫ pullbackMapBase t t' Y.hom a ha =
      pullbackMapBase t t' X.hom a ha ≫ (sliceFiberFunctor t').map f := by
  have htf : (sliceFiberFunctor t).map f ≫ pullback.fst Y.hom t =
      pullback.fst X.hom t ≫ f.left := sliceFiberFunctor_map_fst t f
  have hts : (sliceFiberFunctor t).map f ≫ pullback.snd Y.hom t =
      pullback.snd X.hom t := sliceFiberFunctor_map_snd t f
  have htf' : (sliceFiberFunctor t').map f ≫ pullback.fst Y.hom t' =
      pullback.fst X.hom t' ≫ f.left := sliceFiberFunctor_map_fst t' f
  have hts' : (sliceFiberFunctor t').map f ≫ pullback.snd Y.hom t' =
      pullback.snd X.hom t' := sliceFiberFunctor_map_snd t' f
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMapBase_fst, htf, Category.assoc, htf',
      ← Category.assoc, pullbackMapBase_fst]
  · rw [Category.assoc, pullbackMapBase_snd, ← Category.assoc, hts,
      Category.assoc, hts', pullbackMapBase_snd]

end SerrePositivity.KST.SConstruction
