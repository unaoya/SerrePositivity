module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanIntervalEvaluation

/-!
概要：長 Hom の全族を、二つの K 座標を分離した空間へ延長する。
方針：対角上では元の全区間を保持し、合成端では分離した二入力の合成を指定する。
規約：K と補助パラメーター L は任意。標的 H の Kan 性だけを使う。
使われ方：短辺の別々の path 座標と、元の長 Hom の全族を同時に扱う。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- K の対角を補助パラメーター L 全体で保つ包含。 -/
def triangleParameterDiagonal (K L : SSet.{u}) : K ⊗ L ⟶ (K ⊗ K) ⊗ L :=
  lift (lift (fst K L) (fst K L)) (snd K L)

/-- 同じ包含には、最初の K 座標を保つ厳密左逆がある。 -/
lemma triangleParameterDiagonal_retract (K L : SSet.{u}) :
    triangleParameterDiagonal K L ≫
      lift (fst (K ⊗ K) L ≫ fst K K) (snd (K ⊗ K) L) = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨k, l⟩
  rfl

instance triangleParameterDiagonal_mono (K L : SSet.{u}) :
    Mono (triangleParameterDiagonal K L) :=
  mono_of_mono_fac (triangleParameterDiagonal_retract K L)

/-- 元の全区間を対角上で保持し、分離した二短辺の合成を合成端に指定する。 -/
lemma triangleDiagonalKanExtension_exists
    (K L A B H : SSet.{u}) [KanComplex H]
    (f : K ⟶ A) (g : K ⟶ B) (μ : A ⊗ B ⟶ H)
    (q : K ⊗ L ⟶ (ihom (Δ[1] : SSet.{u})).obj H)
    (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      fst K L ≫ lift f g ≫ μ) :
    ∃ Q : (K ⊗ K) ⊗ L ⟶ (ihom (Δ[1] : SSet.{u})).obj H,
      triangleParameterDiagonal K L ≫ Q = q ∧
      Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        lift (fst (K ⊗ K) L ≫ fst K K ≫ f)
          (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫ μ := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let b := lift (fst (K ⊗ K) L ≫ fst K K ≫ f)
    (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫ μ
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIntervalEvaluation_trivialKanFibration H
  have : HasLiftingProperty (triangleParameterDiagonal K L) p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq q (triangleParameterDiagonal K L) p b := ⟨by
    change q ≫ p = triangleParameterDiagonal K L ≫ b
    rw [hq]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨k, l⟩
    rfl⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 同じ延長を実際の区間全族として公開し、対角上で元の全族を厳密に回収する。 -/
lemma triangleDiagonalKanExtension_uncurry_exists
    (K L A B H : SSet.{u}) [KanComplex H]
    (f : K ⟶ A) (g : K ⟶ B) (μ : A ⊗ B ⟶ H)
    (q : K ⊗ L ⟶ (ihom (Δ[1] : SSet.{u})).obj H)
    (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      fst K L ≫ lift f g ≫ μ) :
    ∃ M : (Δ[1] : SSet.{u}) ⊗ ((K ⊗ K) ⊗ L) ⟶ H,
      (Δ[1] ◁ triangleParameterDiagonal K L) ≫ M = uncurry q ∧
      curry M ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := H) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        lift (fst (K ⊗ K) L ≫ fst K K ≫ f)
          (fst (K ⊗ K) L ≫ snd K K ≫ g) ≫ μ := by
  obtain ⟨Q, hQ, hQp⟩ := triangleDiagonalKanExtension_exists K L A B H f g μ q hq
  refine ⟨uncurry Q, ?_, ?_⟩
  · rw [← uncurry_natural_left, hQ]
  · rw [curry_uncurry]
    exact hQp

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
