module

public import SerrePositivity.AlgebraicGeometry.PairedCechGeometry

/-!
概要：同じ二つの増大 nerve の積を、二変数に反変な幾何的図式にする。
方針：既存の nerve 関手の射を pullback.map へ代入し、二つの射影で法則を確認する。
規約：基底写像は同じ始対象からの射の像を保持する。
使われ方：複体値の二重 Čech の自然性（計画 P08〜P10）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元の二つの増大 nerve の写像による、同じ基底上の積の反変な射。 -/
def pairedCechSchemeMap {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {a a' b b' : AugmentedSimplexCategory} (α : a ⟶ a') (β : b ⟶ b') :
    pairedCechScheme h g a' b' ⟶ pairedCechScheme h g a b := by
  let H := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk h).augmentedCechNerve
  let G := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk g).augmentedCechNerve
  refine pullback.map (augmentedNerveBase h a') (augmentedNerveBase g b')
    (augmentedNerveBase h a) (augmentedNerveBase g b)
    (H.map α.op) (G.map β.op) (𝟙 _) ?_ ?_
  · symm
    change H.map α.op ≫ H.map (WithInitial.starInitial.to a).op =
      H.map (WithInitial.starInitial.to a').op ≫ 𝟙 _
    rw [Category.comp_id, ← H.map_comp]
    congr 1
  · symm
    change G.map β.op ≫ G.map (WithInitial.starInitial.to b).op =
      G.map (WithInitial.starInitial.to b').op ≫ 𝟙 _
    rw [Category.comp_id, ← G.map_comp]
    congr 1

/-- 同じ積の射は、二つの恒等射を恒等射へ送る。 -/
theorem pairedCechSchemeMap_id {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (a b : AugmentedSimplexCategory) : pairedCechSchemeMap h g (𝟙 a) (𝟙 b) = 𝟙 _ := by
  let H := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk h).augmentedCechNerve
  let G := AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk g).augmentedCechNerve
  apply pullback.hom_ext
  · simp only [pairedCechSchemeMap, pullback.lift_fst, Category.id_comp]
    change pullback.fst _ _ ≫ H.map (𝟙 (op a)) = pullback.fst _ _
    rw [H.map_id, Category.comp_id]
  · simp only [pairedCechSchemeMap, pullback.lift_snd, Category.id_comp]
    change pullback.snd _ _ ≫ G.map (𝟙 (op b)) = pullback.snd _ _
    rw [G.map_id, Category.comp_id]

/-- 同じ積の射は、二つの増大単体圏の合成を反変な合成へ送る。 -/
theorem pairedCechSchemeMap_comp {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (h : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    {a a' a'' b b' b'' : AugmentedSimplexCategory}
    (α : a ⟶ a') (α' : a' ⟶ a'') (β : b ⟶ b') (β' : b' ⟶ b'') :
    pairedCechSchemeMap h g (α ≫ α') (β ≫ β') =
      pairedCechSchemeMap h g α' β' ≫ pairedCechSchemeMap h g α β := by
  simp only [pairedCechSchemeMap, op_comp, Functor.map_comp, pullback.map_comp, Category.id_comp]

end SerrePositivity.AlgebraicGeometry
