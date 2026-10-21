module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorSimplex
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorNaturality
/-!
概要：全次元 HA と全単調写像への自然性から、元の二つの dg nerve の直積から実 tensor nerve への写像を構成する。
方針：元の実 cochain と HA 方程式を保ち、全面・退化への自然性を使う。
規約：tensor nerve と元の直積を同一視しない。使われ方：二変数 Hom の実 ∞ 関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped BigOperators Simplicial
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
lemma dgNerveTensorSimplex_pullback {m n : ℕ} (s : Simplex R B n) (t : Simplex R C n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    (dgNerveTensorSimplex R B C s t).pullback α =
      dgNerveTensorSimplex R B C (s.pullback α) (t.pullback α) := by
  apply Simplex.ext
  exact dgNerveTensorDataCandidate_naturality R B C s.toSimplexData t.toSimplexData α
open MonoidalCategory Opposite
/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
def dgNerveTensorProductMap (E : Type v) [DGCategory R E] :
    dgNerve R B ⊗ dgNerve R E ⟶ dgNerve R (DGTensorCategory R B E) where
  app _ := ↾fun st => dgNerveTensorSimplex R B E st.1 st.2
  naturality _ _ f := by
    ext st
    exact (dgNerveTensorSimplex_pullback R B E st.1 st.2 f.unop.toOrderHom).symm

/-- 実 tensor 写像は同じ対象対の頂点を回収する。 -/
lemma dgNerveTensorSimplex_vertex (C : Type v) [DGCategory R C] (b : B) (c : C) :
    dgNerveTensorSimplex R B C (Simplex.vertex b) (Simplex.vertex c) =
      Simplex.vertex (A := R) (D := DGTensorCategory R B C) (b, c) := by
  apply Simplex.ext
  refine SimplexData.ext
    (s := (dgNerveTensorSimplex R B C (Simplex.vertex b) (Simplex.vertex c)).toSimplexData)
    (t := (Simplex.vertex (A := R) (D := DGTensorCategory R B C) (b, c)).toSimplexData) ?_ ?_
  · rfl
  · exact zero_hom_heq _ _
/-- 実 tensor 写像は同じ対象対の頂点を回収する。 -/
lemma dgNerveTensorProductMap_vertex (C : Type v) [DGCategory R C] (b : B) (c : C) :
    (dgNerveTensorProductMap R B C).app (op ⦋0⦌) (Simplex.vertex b, Simplex.vertex c) =
      Simplex.vertex (A := R) (D := DGTensorCategory R B C) (b, c) :=
  dgNerveTensorSimplex_vertex R B C b c
end SerrePositivity.InfinityCategories
