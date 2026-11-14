module

public import SerrePositivity.AlgebraicGeometry.BaseChangedOpenTransitionGlueData

/-!
概要：固定模型への射影の後での六種の式を、後段の実際の gluing の式へ移す。
方針：二射影で判定し、三重交叉では具体的な同型を前合成する。
規約：係数射の単射性・忠実平坦性を仮定しない。
使われ方：G2 の同時一致判定で得た式から Scheme.GlueData への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {S B : Scheme.{u}} (C : OpenTransitionCandidate S) (γ : B ⟶ S)

/-- 固定した模型間の六種の式が各底変換の模型への射影の後で成立する。 -/
structure ProjectedModelEquations : Prop where
  diagonalRight : ∀ i, pullback.snd γ (C.p i) ≫ C.d i ≫ C.f i i = pullback.snd γ (C.p i)
  diagonalLeft : ∀ i, pullback.snd γ (C.q i i) ≫ C.f i i ≫ C.d i = pullback.snd γ (C.q i i)
  reverseDiagonal : ∀ i, pullback.snd γ (C.q i i) ≫ C.t i i = pullback.snd γ (C.q i i)
  reverseInverse : ∀ i j, pullback.snd γ (C.q i j) ≫ C.t i j ≫ C.t j i = pullback.snd γ (C.q i j)
  tripleFst : ∀ i j k,
    pullback.snd γ (pullback.fst (C.f i j) (C.f i k) ≫ C.f i j ≫ C.p i) ≫ C.L i j k ≫ C.f j k =
      pullback.snd γ (pullback.fst (C.f i j) (C.f i k) ≫ C.f i j ≫ C.p i) ≫
        pullback.fst (C.f i j) (C.f i k) ≫ C.t i j ≫ C.f j i
  tripleSnd : ∀ i j k,
    pullback.snd γ (pullback.fst (C.f i j) (C.f i k) ≫ C.f i j ≫ C.p i) ≫
        C.L i j k ≫ C.t j k ≫ C.f k j =
      pullback.snd γ (pullback.fst (C.f i j) (C.f i k) ≫ C.f i j ≫ C.p i) ≫
        pullback.snd (C.f i j) (C.f i k) ≫ C.t i k ≫ C.f k i

/-- 固定模型への射影の式から、実際の後段の六種の式を供給する。 -/
theorem baseChangedEquations_of_projected (h : C.ProjectedModelEquations γ) :
    C.BaseChangedEquations γ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simpa [baseChangedD, baseChangedF, Category.assoc] using h.diagonalRight i
  · intro i
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simpa [baseChangedD, baseChangedF, Category.assoc] using h.diagonalLeft i
  · intro i
    apply pullback.hom_ext
    · simp
    · simpa [baseChangedT, Category.assoc] using h.reverseDiagonal i
  · intro i j
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simpa [baseChangedT, Category.assoc] using h.reverseInverse i j
  · intro i j k
    apply pullback.hom_ext
    · simp [Category.assoc]
    · have he := congrArg
        (fun z ↦ (baseChangedModelTripleIso γ (C.p i) (C.q i j) (C.q i k)
          (C.f i j) (C.f i k) (C.fOver i j) (C.fOver i k)).hom ≫ z) (h.tripleFst i j k)
      simpa [baseChangedL, baseChangedF, baseChangedT, Category.assoc,
        baseChangedModelTripleComparison, cartesianPullbackMap] using he
  · intro i j k
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangedF_toBase, baseChangedT_toBase, baseChangedL_toBase]
      have he := congrArg (fun z ↦ z ≫ pullback.fst γ (C.p i))
        (pullback.condition (f := C.baseChangedF γ i j) (g := C.baseChangedF γ i k))
      simpa only [Category.assoc, baseChangedF_toBase] using he
    · have he := congrArg
        (fun z ↦ (baseChangedModelTripleIso γ (C.p i) (C.q i j) (C.q i k)
          (C.f i j) (C.f i k) (C.fOver i j) (C.fOver i k)).hom ≫ z) (h.tripleSnd i j k)
      simpa [baseChangedL, baseChangedF, baseChangedT, Category.assoc,
        baseChangedModelTripleComparison, cartesianPullbackMap] using he

end SerrePositivity.AlgebraicGeometry.OpenTransitionCandidate
