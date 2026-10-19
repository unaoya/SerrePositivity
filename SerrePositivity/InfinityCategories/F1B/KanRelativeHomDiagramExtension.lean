module

public import SerrePositivity.InfinityCategories.F1B.KanPullbackRestrictionSquare
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianInnerAnodynePullback

/-!
概要：cocartesian fibration 間の単射による図式の制限で、内ホーン上の延長を同時に固定する。
方針：両側の内ホーン逆像の前合成同値と、自然性の pullback 四角形を使う。
規約：底の quasicategory 性は不要。
使われ方：相対指数の制限射自体の inner fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：内ホーンの逆像上の図式は、指定された部分図式を保って全逆像へ延長できる。
方針：部分図式の逆像とホーンの逆像を pushout で貼り、前合成同値で延長する。
規約：固定する底上の射は単射で、両射影は cocartesian fibration。
使われ方：相対指数の制限の内ホーン持ち上げ。 -/
lemma exists_kanRelativeHomDiagram_extension {C D : SSet.{u}} [Quasicategory D]
    {K L A B : Over C} (i : K ⟶ L) [Mono i.left]
    [CocartesianFibration K.hom] [CocartesianFibration L.hom]
    (u : A ⟶ B) (hu : innerHornInclusions u.left)
    (F : pullback B.hom K.hom ⟶ D) (G : pullback A.hom L.hom ⟶ D)
    (hFG : (overPullbackUnderlying K.hom).map u ≫ F = overPullbackMap i A ≫ G) :
    ∃ H : pullback B.hom L.hom ⟶ D,
      overPullbackMap i B ≫ H = F ∧ (overPullbackUnderlying L.hom).map u ≫ H = G := by
  have hm : ∀ {X Y : SSet.{u}} (f : X ⟶ Y), innerHornInclusions f → Mono f := by
    intro X Y f hf
    cases hf
    infer_instance
  have : Mono u.left := hm u.left hu
  have : Mono u := (Over.forget C).mono_of_mono_map (show Mono u.left from inferInstance)
  exact exists_kanPrecompositionSquare_extension
    ((overPullbackUnderlying K.hom).map u) (overPullbackMap i A) (overPullbackMap i B)
    ((overPullbackUnderlying L.hom).map u) (kanOverPullbackMap_naturality_isPullback i u)
    (kanCocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence K.hom u hu)
    (kanCocartesianFibration_overPullback_innerHorn_isPrecompositionEquivalence L.hom u hu)
    F G hFG

end SerrePositivity.InfinityCategories.F1B
