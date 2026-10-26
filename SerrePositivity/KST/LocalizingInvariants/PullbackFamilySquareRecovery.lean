module

public import SerrePositivity.KST.LocalizingInvariants.ParametricPullbackFamilyTranspose

/-!
概要：補完済みの同じ実 pullback 全族から、全正方形と元の二脚を厳密に復元する。
方針：元の包含後の全族を逆転置し、二度の転置恒等と各変数の自然性を使う。
規約：別の pullback を選ばず、元の cospan と指定終端列の全単体写像を保持する。
使われ方：実余錐円柱の全前段比較に、元の分母経路を一次単体のまま回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

local instance recoveredSquareFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance recoveredSquareParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

/-- 同じ実 pullback 全族の包含を逆転置した全正方形。 -/
def pullbackFamilySquare {P L X : SSet.{u}}
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X)) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X) :=
  spanDiagramFamilyTranspose
    (F ≫ (ihom L).map (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι)

lemma pullbackFamilySquare_family {P L X : SSet.{u}}
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X)) :
    parametricPullbackSquares (pullbackFamilySquare F) =
      F ≫ (ihom L).map (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι :=
  spanDiagramFamilyTranspose_transpose _

lemma pullbackFamilySquare_parametric {P L X : SSet.{u}} [Quasicategory X] [IsStable X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q) :
    pullbackFamilySquare (parametricPullbackDiagramFamily Q hQ) = Q := by
  rw [pullbackFamilySquare, parametricPullbackDiagramFamily_ι]
  exact spanDiagramFamilyTranspose_transpose Q

lemma pullbackFamilySquare_pre_diagram {P L L' X : SSet.{u}} (j : L' ⟶ L)
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X)) :
    pullbackFamilySquare (F ≫ (pre j).app (pullbackDiagrams X)) =
      pullbackFamilySquare F ≫ (pre j).app ((ihom P).obj X) := by
  rw [pullbackFamilySquare, Category.assoc, ← (pre j).naturality,
    ← Category.assoc, spanDiagramFamilyTranspose_pre_diagram]
  rfl

lemma pullbackFamilySquare_cospan {P L X : SSet.{u}}
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X)) :
    cospanSquareBoundary ≫ pullbackFamilySquare F =
      spanDiagramFamilyTranspose (F ≫ (ihom L).map (pullbackProjection X)) := by
  rw [pullbackFamilySquare, ← spanDiagramFamilyTranspose_pre_parameter,
    Category.assoc, ← Functor.map_comp]
  rfl

/-- 同じ cospan を持つ実補完から戻した全正方形も、元の全 cospan に一致する。 -/
lemma pullbackFamilySquare_cospan_eq {P L X : SSet.{u}} [Quasicategory X] [IsStable X]
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q)
    (hF : F ≫ (ihom L).map (pullbackProjection X) =
      parametricPullbackDiagramFamily Q hQ ≫ (ihom L).map (pullbackProjection X)) :
    cospanSquareBoundary ≫ pullbackFamilySquare F = cospanSquareBoundary ≫ Q := by
  rw [pullbackFamilySquare_cospan, hF, parametricPullbackDiagramFamily_projection,
    spanDiagramFamilyTranspose_transpose]

/-- 指定図式上で一致した実補完は、逆転置後もその同じ全制限に一致する。 -/
lemma pullbackFamilySquare_restriction_eq {P L L' X : SSet.{u}}
    [Quasicategory X] [IsStable X] (j : L' ⟶ L)
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q)
    (hF : F ≫ (pre j).app (pullbackDiagrams X) =
      parametricPullbackDiagramFamily Q hQ ≫ (pre j).app (pullbackDiagrams X)) :
    pullbackFamilySquare F ≫ (pre j).app ((ihom P).obj X) =
      Q ≫ (pre j).app ((ihom P).obj X) := by
  rw [← pullbackFamilySquare_pre_diagram, hF, pullbackFamilySquare_pre_diagram,
    pullbackFamilySquare_parametric]

lemma pullbackFamilySquare_right_eq {P L X : SSet.{u}} [Quasicategory X] [IsStable X]
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q)
    (hF : F ≫ (ihom L).map (pullbackProjection X) =
      parametricPullbackDiagramFamily Q hQ ≫ (ihom L).map (pullbackProjection X)) :
    squareRightEdge ≫ pullbackFamilySquare F = squareRightEdge ≫ Q := by
  have he := congrArg (fun f => horn₂₂.ι₀₂ ≫ f)
    (pullbackFamilySquare_cospan_eq F Q hQ hF)
  simpa only [← Category.assoc, cospanSquareBoundary_rightEdge] using he

lemma pullbackFamilySquare_top_eq {P L X : SSet.{u}} [Quasicategory X] [IsStable X]
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q)
    (hF : F ≫ (ihom L).map (pullbackProjection X) =
      parametricPullbackDiagramFamily Q hQ ≫ (ihom L).map (pullbackProjection X)) :
    squareTopEdge ≫ pullbackFamilySquare F = squareTopEdge ≫ Q := by
  have he := congrArg (fun f => horn₂₂.ι₁₂ ≫ f)
    (pullbackFamilySquare_cospan_eq F Q hQ hF)
  simpa only [← Category.assoc, cospanSquareBoundary_topEdge] using he

/-- 元の終端全列は、復元後の正方形の終端評価そのものとして一致する。 -/
lemma pullbackFamilySquare_last_eq {P X : SSet.{u}} [Quasicategory X] [IsStable X]
    {n : ℕ} (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q)
    (hF : F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      parametricPullbackDiagramFamily Q hQ ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) :
    pullbackFamilySquare F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  have he := congrArg (fun f => f ≫
    evaluateFunctorAt (Y := (ihom P).obj X) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    (pullbackFamilySquare_restriction_eq (simplexLastPoint n) F Q hQ hF)
  rw [Category.assoc, Category.assoc, stable_pre_evaluateFunctorAt] at he
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  rwa [hp] at he

/-- 復元した同じ全正方形の各評価は、元の実 pullback 頂点そのもの。 -/
lemma pullbackFamilySquare_evaluate {P L X : SSet.{u}}
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X)) (l : L _⦋0⦌) (p : P _⦋0⦌) :
    pullbackFamilySquare F ≫ evaluateFunctorAt l ≫ evaluateFunctorAt p =
      (functorVertexEquiv _ X).symm
        ((F ≫ evaluateFunctorAt (Y := pullbackDiagrams X) l).app (Opposite.op ⦋0⦌) p).val := by
  have he := parametricPullbackSquares_evaluate (pullbackFamilySquare F) p l
  rw [pullbackFamilySquare_family] at he
  have hn : (ihom L).map (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
      evaluateFunctorAt (Y := (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) l =
      evaluateFunctorAt (Y := pullbackDiagrams X) l ≫
        (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι := rfl
  change ((F ≫ (ihom L).map (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
    evaluateFunctorAt l).app (Opposite.op ⦋0⦌) p) = _ at he
  rw [hn] at he
  apply (functorVertexEquiv _ X).injective
  rw [Equiv.apply_symm_apply]
  exact he.symm

lemma pullbackFamilySquare_isPullback {P L X : SSet.{u}} [Quasicategory X] [IsStable X]
    (F : P ⟶ (ihom L).obj (pullbackDiagrams X)) :
    IsPullbackSquare (pullbackFamilySquare F) := by
  apply (isPullbackSquare_functor_iff _).mpr
  intro l
  apply (isPullbackSquare_functor_iff _).mpr
  intro p
  rw [Category.assoc, pullbackFamilySquare_evaluate]
  exact fullSubcomplexOnVertices_vertex
    ((F ≫ evaluateFunctorAt (Y := pullbackDiagrams X) l).app (Opposite.op ⦋0⦌) p)

end SerrePositivity.KST.LocalizingInvariants
