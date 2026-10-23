module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullback
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorCompositionLaws

/-!
概要：相対写像空間の底変換の単位則と合成則。
方針：相対 uncurry と引き戻しの二射影で等式を判定する。
規約：いずれも単体集合の射の厳密な等式。
使われ方：Kerodon §5.3.1、底変換の豊穣関手性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対写像空間の底変換は豊穣単位を保つ。
方針：uncurry 後の第一射影で右単位子の自然性を用いる。
規約：引き戻した対象を Over.mk で表示する。
使われ方：Kerodon §5.3.1、底変換の豊穣単位則。 -/
lemma relativeFunctorPullback_identity {B D : SSet.{u}} (a : Over B) (k : D ⟶ B) :
    relativeFunctorIdentity a ≫ relativeFunctorPullback a.hom a.hom k =
      relativeFunctorIdentity (Over.mk (pullback.snd a.hom k)) := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [relativeFunctorPullback_uncurry_fst, relativeFunctorIdentity,
      relativeFunctorUncurry_curry, relativeFunctorIdentity, relativeFunctorUncurry_curry]
    exact (rightUnitor_naturality (pullback.fst a.hom k)).symm
  · rw [relativeFunctorUncurry_projection, relativeFunctorIdentity,
      relativeFunctorUncurry_curry]
    rfl

/-- 概要：相対写像空間の底変換は豊穣合成を保つ。
方針：二射影で比較し、第一射影では二つの相対評価を順に計算する。
規約：底上の三つの対象を同じ k に沿って引き戻す。
使われ方：Kerodon §5.3.1、底変換の豊穣合成則。 -/
lemma relativeFunctorPullback_composition {B D : SSet.{u}}
    (a b c : Over B) (k : D ⟶ B) :
    relativeFunctorComposition a b c ≫ relativeFunctorPullback a.hom c.hom k =
      (relativeFunctorPullback a.hom b.hom k ⊗ₘ relativeFunctorPullback b.hom c.hom k) ≫
        relativeFunctorComposition (Over.mk (pullback.snd a.hom k))
          (Over.mk (pullback.snd b.hom k)) (Over.mk (pullback.snd c.hom k)) := by
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · rw [relativeFunctorPullback_uncurry_fst]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    have hf := congrArg (fun z : pullback a.hom k ⊗ relativeFunctorSpace b.hom a.hom ⟶ b.left ↦ z.app n (x, f))
      (relativeFunctorPullback_uncurry_fst a.hom b.hom k (𝟙 _))
    let y := ((relativeFunctorPullback a.hom b.hom k).app n f).val.app n (𝟙 _) x
    have hg := congrArg (fun z : pullback b.hom k ⊗ relativeFunctorSpace c.hom b.hom ⟶ c.left ↦ z.app n (y, g))
      (relativeFunctorPullback_uncurry_fst b.hom c.hom k (𝟙 _))
    exact (hg.trans (congrArg (fun t ↦ g.val.app n (𝟙 _) t) hf)).symm
  · rw [relativeFunctorUncurry_projection, relativeFunctorUncurry_projection]

end SerrePositivity.InfinityCategories
