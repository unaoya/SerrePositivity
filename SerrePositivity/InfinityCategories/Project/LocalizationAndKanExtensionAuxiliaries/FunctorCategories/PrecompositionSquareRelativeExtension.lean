module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionSquareExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionRelativeLifting

/-!
概要：同値な横辺を持つ引き戻し四角形で、標的で指定された全図式を保って延長する。
方針：二部分の和の全体への包含に関する相対持ち上げを使う。
規約：標的の射には単射な前合成同値に対する持ち上げを明示的に要求する。
使われ方：変動する添字の相対比較の内ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二部分上の図式を、標的で指定した全図式の上で同時に延長できる。
方針：和の包含が単射な前合成同値となることを示し、その持ち上げ性を適用する。
規約：hU は標的の射に対する持ち上げ条件であり、追加の公理ではない。
使われ方：相対指数の制限と標的への後合成を同時に指定した延長。 -/
lemma exists_kanPrecompositionSquare_extension_over {A B C T D E : SSet.{u}}
    (i : A ⟶ B) (g : A ⟶ C) (k : B ⟶ T) (j : C ⟶ T)
    [Mono i] [Mono k] [Mono j] (hs : IsPullback i g k j)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence j)
    (U : D ⟶ E)
    (hU : ∀ {X Y : SSet.{u}} (m : X ⟶ Y), Mono m →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence m → HasLiftingProperty m U)
    (F : B ⟶ D) (G : C ⟶ D) (H₀ : T ⟶ E)
    (hFG : i ≫ F = g ≫ G) (hF : F ≫ U = k ≫ H₀) (hG : G ≫ U = j ≫ H₀) :
    ∃ H : T ⟶ D, k ≫ H = F ∧ j ≫ H = G ∧ H ≫ U = H₀ := by
  let hp := IsPushout.of_hasPushout i g
  let m := hp.desc k j hs.w
  have hmMono : Mono m := hp.desc_mono_of_isPullback hs
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (pushout.inr i g) := hi.of_isPushout hp
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence m := by
    apply he.cancel_left
    rw [show pushout.inr i g ≫ m = j from hp.inr_desc _ _ _]
    exact hj
  let a := hp.desc F G hFG
  have sq : CommSq a m U H₀ := by
    constructor
    dsimp only [a]
    apply hp.hom_ext
    · rw [← Category.assoc, hp.inl_desc F G hFG, hF, ← Category.assoc]
      rw [show pushout.inl i g ≫ m = k from hp.inl_desc _ _ _]
    · rw [← Category.assoc, hp.inr_desc F G hFG, hG, ← Category.assoc]
      rw [show pushout.inr i g ≫ m = j from hp.inr_desc _ _ _]
  have : HasLiftingProperty m U := hU m hmMono hm
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [← hp.inl_desc k j hs.w, Category.assoc, sq.fac_left]
    exact hp.inl_desc F G hFG
  · rw [← hp.inr_desc k j hs.w, Category.assoc, sq.fac_left]
    exact hp.inr_desc F G hFG

/-- 概要：単射による関手の制限を標的の射とする相対延長が存在する。
方針：単射な前合成同値は関手の制限に対する左持ち上げ性を持つことを使う。
規約：X だけに quasicategory 性を要求する。
使われ方：境界を固定した関手圏の V′ に対する相対 Kan の組み立て。 -/
lemma exists_kanPrecompositionSquare_extension_over_pre {A B C T P Q X : SSet.{u}}
    [Quasicategory X] (i : A ⟶ B) (g : A ⟶ C) (k : B ⟶ T) (j : C ⟶ T)
    [Mono i] [Mono k] [Mono j] (hs : IsPullback i g k j)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence j)
    (v : P ⟶ Q) [Mono v]
    (F : B ⟶ (ihom Q).obj X) (G : C ⟶ (ihom Q).obj X) (H₀ : T ⟶ (ihom P).obj X)
    (hFG : i ≫ F = g ≫ G)
    (hF : F ≫ (pre v).app X = k ≫ H₀) (hG : G ≫ (pre v).app X = j ≫ H₀) :
    ∃ H : T ⟶ (ihom Q).obj X,
      k ≫ H = F ∧ j ≫ H = G ∧ H ≫ (pre v).app X = H₀ := by
  apply exists_kanPrecompositionSquare_extension_over i g k j hs hi hj ((pre v).app X) ?_
    F G H₀ hFG hF hG
  intro Y Z m hm he
  have : Mono m := hm
  exact he.hasLiftingProperty_pre v X

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
