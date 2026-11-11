module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square

/-!
概要：有限格子の単調写像を、標準単体の直積からの全単体的写像へ移す。
方針：二つの単体の頂点列を同じ添字で評価し、格子の単調写像へ続ける。
規約：元の有限順序写像を保持。使われ方：右辺正方形の対角による分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants

variable {m n k : ℕ}

def gridMap (F : Fin (m + 1) × Fin (n + 1) →o Fin (k + 1)) :
    (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ Δ[k] where
  app d := by
    obtain ⟨⟨d⟩⟩ := d
    exact ↾fun s ↦ stdSimplex.objEquiv.symm (SimplexCategory.mkHom {
      toFun := fun i ↦ F (s.1 i, s.2 i)
      monotone' := fun _ _ h ↦ F.monotone
        ⟨(stdSimplex.asOrderHom s.1).monotone h, (stdSimplex.asOrderHom s.2).monotone h⟩ })
  naturality := by
    intro d e α
    apply ConcreteCategory.hom_ext
    intro s
    apply SSet.stdSimplex.ext
    intro i
    rfl

lemma gridMap_apply (F : Fin (m + 1) × Fin (n + 1) →o Fin (k + 1)) {d : ℕ}
    (s : (Δ[m] : SSet.{u}) _⦋d⦌) (t : (Δ[n] : SSet.{u}) _⦋d⦌) (i : Fin (d + 1)) :
    (gridMap F).app (Opposite.op ⦋d⦌) (s, t) i = F (s i, t i) := rfl

end SerrePositivity.KST.LocalizingInvariants
