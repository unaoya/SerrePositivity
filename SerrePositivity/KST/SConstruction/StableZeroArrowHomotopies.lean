module
public import SerrePositivity.KST.SConstruction.StableZeroArrowComparisons
public import SerrePositivity.KST.SConstruction.HomotopyEndpointEvaluation

/-!
概要：共有零対角の二全ホモトピーは同じ両端経路から同じ射の類を持つ。
方針：元の可逆二比較を全関手同型にし、既存の零辺比較の一意性を適用する。
規約：元両ホモトピー・指定全経路を保持。使われ方：上下全比較の対角代表修正。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：元零完全射からの二可逆ホモトピーは同じ端点経路なら同じ全射の類を持つ。
方針：元二比較同型の両端評価を照合し、零辺の比較一意性を使う。
規約：同じ元ホモトピーの類。使われ方：共有零対角の全比較の照合。 -/
lemma stableZeroArrowHomotopy_homMk_eq (A B : StableCategory.{u}) (F : ExactMap A B)
    (hF : ∀ x, IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x))
    {g : (Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u}}
    (H J : SSet.Homotopy (SSet.yonedaEquiv.symm (stableArrow F).edge) g)
    (hH : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H))
    (hJ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy J))
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ J.h)
    (h₁ : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ J.h) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  let e : FunctorIso (SSet.yonedaEquiv.symm (stableArrow F).edge) g :=
    @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) hH
  let e' : FunctorIso (SSet.yonedaEquiv.symm (stableArrow F).edge) g :=
    @asIso _ _ _ _ (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J)) hJ
  have hv₀ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by
    apply stdSimplex.obj₀Equiv.injective
    rfl
  have hv₁ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u + 1}) ⟶ Δ[1]) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    apply stdSimplex.obj₀Equiv.injective
    rfl
  let P (x : (Δ[1] : SSet.{u + 1}) _⦋0⦌) : Prop :=
    (hoFunctor.map (evaluateFunctorAt (Y := StableInfinity.{u}) x)).toFunctor.map e.hom =
      (hoFunctor.map (evaluateFunctorAt (Y := StableInfinity.{u}) x)).toFunctor.map e'.hom
  have hp₀ : P (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))) :=
    homotopyEvaluation_eq_of_endpoint H J 1 h₀
  have hp₁ : P (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))) :=
    homotopyEvaluation_eq_of_endpoint H J 0 h₁
  have he : e = e' := stableZeroArrowFunctorIso_ext A B F hF e e'
    ((congrArg P hv₀).mp hp₀) ((congrArg P hv₁).mp hp₁)
  exact congrArg Iso.hom he

/-- 概要：元対角表示を保ったまま、零完全射の二比較の類を照合できる。
方針：元辺との指定等号を使って前補題へ移す。
規約：元の比較・元一単体を変更しない。使われ方：実四角形の共有対角。 -/
lemma stableZeroSourceHomotopy_homMk_eq (A B : StableCategory.{u}) (F : ExactMap A B)
    (hF : ∀ x, IsZeroVertex (F.hom.app (Opposite.op ⦋0⦌) x))
    {f g : (Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u}}
    (hf : SSet.yonedaEquiv.symm (stableArrow F).edge = f) (H J : SSet.Homotopy f g)
    (hH : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H))
    (hJ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy J))
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ J.h)
    (h₁ : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ H.h =
      (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ J.h) :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy J) := by
  subst f
  exact stableZeroArrowHomotopy_homMk_eq A B F hF H J hH hJ h₀ h₁
end SerrePositivity.KST.SConstruction
