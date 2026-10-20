module

public import SerrePositivity.KST.LocalizingInvariants.FullSubcomplexReflection
public import SerrePositivity.InfinityCategories.Stable.BicartesianCriterion
public import SerrePositivity.InfinityCategories.Stable.CofiberZeroSource

/-!
概要：全部分複体へ四角形と指定 fiber・cofiber を制限する。
方針：四頂点の条件で元の全単体を持ち上げ、錐の普遍性は包含で反映する。
規約：指定辺を厳密に保つ。使われ方：通常 pullback の閉性から実安定性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FullSubcomplex

variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

def squareLift (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hP : ∀ i j : Fin 2, P (squareVertex F i j)) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (fullSubcomplexOnVertices X P : SSet.{u}) :=
  fullSubcomplexLift P F (by
    rintro ⟨a, b⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective a
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective b
    exact hP i j)

lemma squareLift_ι (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hP : ∀ i j : Fin 2, P (squareVertex F i j)) :
    squareLift P F hP ≫ (fullSubcomplexOnVertices X P).ι = F := fullSubcomplexLift_ι _ _ _

lemma reflects_pullback (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶
    (fullSubcomplexOnVertices X P : SSet.{u}))
    (hF : IsPullbackSquare (F ≫ (fullSubcomplexOnVertices X P).ι)) :
    IsPullbackSquare F := reflects_limit P (pullbackCone F) hF

lemma reflects_pushout (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶
    (fullSubcomplexOnVertices X P : SSet.{u}))
    (hF : IsPushoutSquare (F ≫ (fullSubcomplexOnVertices X P).ι)) :
    IsPushoutSquare F := reflects_colimit P (pushoutCocone F) hF

lemma squareLift_zero (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hP : ∀ i j : Fin 2, P (squareVertex F i j))
    (hz : IsZeroVertex (squareVertex F 0 1)) :
    IsZeroVertex (squareVertex (squareLift P F hP) 0 1) := reflects_zero P _ hz

lemma squareLift_edge (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X)
    (hP : ∀ i j : Fin 2, P (squareVertex F i j))
    (δ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1])
    {x y : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj
      (fullSubcomplexOnVertices X P : SSet.{u})) x y)
    (hf : δ ≫ F = SSet.yonedaEquiv.symm
      (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι)).edge) :
    δ ≫ squareLift P F hP = SSet.yonedaEquiv.symm f.edge := by
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).1
  rw [Category.assoc, squareLift_ι, hf, SSet.yonedaEquiv_symm_comp]
  rfl

variable {x y : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌}
  (f : Truncated.Edge (X := (truncation 2).obj
    (fullSubcomplexOnVertices X P : SSet.{u})) x y)

def cofiberLift
    (s : CofiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι)))
    (hP : ∀ i j : Fin 2, P (squareVertex s.square i j)) : CofiberSquare f where
  square := squareLift P s.square hP
  zero_corner := squareLift_zero P s.square hP s.zero_corner
  bottom_edge := squareLift_edge P s.square hP squareBottomEdge f s.bottom_edge
  isPushout := reflects_pushout P _ (by rw [squareLift_ι]; exact s.isPushout)

def fiberLift
    (s : FiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι)))
    (hP : ∀ i j : Fin 2, P (squareVertex s.square i j)) : FiberSquare f where
  square := squareLift P s.square hP
  zero_corner := squareLift_zero P s.square hP s.zero_corner
  right_edge := squareLift_edge P s.square hP squareRightEdge f s.right_edge
  isPullback := reflects_pullback P _ (by rw [squareLift_ι]; exact s.isPullback)

end SerrePositivity.KST.LocalizingInvariants.FullSubcomplex
