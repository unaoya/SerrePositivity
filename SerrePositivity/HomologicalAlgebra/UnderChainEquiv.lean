module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# under 圏の射列の先頭の構造射による表示

## 概要
under 圏の射列を、底の同じ射列と先頭への一つの構造射の組に同一視する。

## 方針
全後続の構造射は先頭の構造射と底の合成で復元する。

## 規約
対象の同値だけでなく、底の射による前合成と全単体作用素に対する式を保持する。

## 使われ方
Weibel §2.2、HA 1.2.4。bar 重みの各次数を自由表現可能前層の余積へ表示する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite
namespace SerrePositivity.HomologicalAlgebra
variable {J : Type} [SmallCategory J]

/-- 底の射列と先頭への構造射から、元の under 圏の射列を構成する。 -/
def underChainOfPair {n : ℕ} (x : J) (s : ComposableArrows J n) (f : x ⟶ s.obj 0) :
    ComposableArrows (Under x) n :=
  s.toUnder x (fun i => f ≫ s.map (homOfLE (Fin.zero_le i))) (by
    intro i j g
    rw [Category.assoc, ← s.map_comp]
    rfl)

/-- under 圏の射列は、底の射列と先頭への一つの構造射と同値。 -/
def underChainPairEquiv (x : J) (n : ℕ) :
    ComposableArrows (Under x) n ≃
      (Σ s : ComposableArrows J n, x ⟶ s.obj 0) where
  toFun τ := ⟨τ ⋙ Under.forget x, (τ.obj 0).hom⟩
  invFun w := underChainOfPair x w.1 w.2
  left_inv τ := by
    refine CategoryTheory.Functor.ext (fun i => ?_) ?_
    · change Under.mk ((τ.obj 0).hom ≫ (τ.map (homOfLE (Fin.zero_le i))).right) =
        Under.mk (τ.obj i).hom
      rw [(τ.map (homOfLE (Fin.zero_le i))).w]
    · intro i j f
      apply (Under.forget x).map_injective
      simp
      rfl
  right_inv w := by
    rcases w with ⟨s, f⟩
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change f ≫ s.map (𝟙 (0 : Fin (n + 1))) = f
    rw [s.map_id, Category.comp_id]

/-- 底の前合成は、同じ底の射列を保ち先頭の構造射だけを合成する。 -/
theorem underChainPairEquiv_map {x y : J} (f : x ⟶ y) {n : ℕ}
    (τ : ComposableArrows (Under y) n) :
    underChainPairEquiv x n (τ ⋙ Under.map f) =
      ⟨τ ⋙ Under.forget y, f ≫ (τ.obj 0).hom⟩ := rfl

/-- 底の射列の先頭を恒等射で持ち上げた、同じ標準 under 射列。 -/
def underScaffold {n : ℕ} (s : ComposableArrows J n) :
    ComposableArrows (Under (s.obj 0)) n := underChainOfPair (s.obj 0) s (𝟙 _)

/-- 標準持ち上げを底へ戻すと元の射列に厳密に一致する。 -/
@[simp]
theorem underScaffold_forget {n : ℕ} (s : ComposableArrows J n) :
    underScaffold s ⋙ Under.forget (s.obj 0) = s := rfl

/-- 元の under 射列は、同じ標準持ち上げと先頭の構造射の前合成で復元できる。 -/
theorem underScaffold_factorization {x : J} {n : ℕ}
    (τ : ComposableArrows (Under x) n) :
    underScaffold (τ ⋙ Under.forget x) ⋙ Under.map (τ.obj 0).hom = τ := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · change Under.mk ((τ.obj 0).hom ≫ 𝟙 _ ≫ (τ.map (homOfLE (Fin.zero_le i))).right) =
      Under.mk (τ.obj i).hom
    rw [Category.id_comp, (τ.map (homOfLE (Fin.zero_le i))).w]
  · intro i j f
    apply (Under.forget x).map_injective
    simp
    rfl

end SerrePositivity.HomologicalAlgebra
