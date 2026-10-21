module

public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyZeroTriangle

/-!
概要：完全関手による矢印圏上の後合成も完全で、矢印の零性は両端の零性で判定できる。
方針：評価と後合成の厳密な交換を両端による完全性判定へ渡す。
規約：元の内部 Hom を保持。使われ方：点ごとの分母を安定な核の cofiber 分母に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma arrowMap_evaluation {X Y : SSet.{u}} (F : X ⟶ Y) (i : Fin 2) :
    (ihom (Δ[1] : SSet.{u})).map F ≫
        evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm i) =
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i) ≫ F := rfl

instance arrowMap_isExact {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
    [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F] :
    IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F) := by
  have h₀ : IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F ≫
      evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [arrowMap_evaluation]
    infer_instance
  have h₁ : IsExactFunctor ((ihom (Δ[1] : SSet.{u})).map F ≫
      evaluateFunctorAt (Y := Y) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [arrowMap_evaluation]
    infer_instance
  exact arrow_exact_of_endpoints Y _

def stableArrowCategory (A : StableCategory.{u}) : StableCategory.{u} :=
  ⟨(ihom (Δ[1] : SSet.{u})).obj A.obj, inferInstance, inferInstance⟩

def exactArrowMap {A B : StableCategory.{u}} (F : ExactMap A B) :
    ExactMap (stableArrowCategory A) (stableArrowCategory B) :=
  ⟨(ihom (Δ[1] : SSet.{u})).map F.hom, inferInstance⟩

lemma arrowVertex_isZero_iff {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    IsZeroVertex v ↔ ∀ i : Fin 2, IsZeroVertex
      ((evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i)).app (Opposite.op ⦋0⦌) v) := by
  constructor
  · intro hv i
    fin_cases i
    · exact IsExactFunctor.preservesZero
        (F := evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) _ hv
    · exact IsExactFunctor.preservesZero
        (F := evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) _ hv
  · intro hv
    obtain ⟨f, rfl⟩ := (functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective v
    have hf : ∀ x : (Δ[1] : SSet.{u}) _⦋0⦌,
        IsZeroVertex (f.app (Opposite.op ⦋0⦌) x) := by
      intro x
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
      have hi := hv i
      change IsZeroVertex ((evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i)).app
        (Opposite.op ⦋0⦌) (functorVertex f)) at hi
      rw [evaluateFunctorAt_functorVertex] at hi
      exact hi
    exact ⟨isInitialVertex_functorVertex_of_pointwise f (fun x => (hf x).1),
      isTerminalVertex_functorVertex_of_pointwise f (fun x => (hf x).2)⟩

end SerrePositivity.KST.LocalizingInvariants
