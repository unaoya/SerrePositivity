module
public import SerrePositivity.KST.SConstruction.StableZeroTriangleDiagonal
public import SerrePositivity.KST.SConstruction.SquareFrameTriangleDiagonals

/-!
概要：零角を通る元四角形の共有対角を、同じ全零完全関手として回収する。
方針：元上二単体の対角を読み、元四角形の対角包含と照合する。
規約：元全四角形と元対角を保持。使われ方：上下二胞体比較の共有対角整列。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (f : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ StableInfinity.{u})

/-- 概要：元四角形の共有対角は元上二単体の同じ完全射。
方針：同じ上二単体の全豊穣作用を読む。規約：対角を選び直さない。
使われ方：元共有対角の零性と比較一意性。 -/
def stableSquareDiagonalMap : ExactMap
    ((SSet.yonedaEquiv (squareTriangle 0 ≫ f)).obj ⟨ULift.up (0 : Fin 3)⟩)
    ((SSet.yonedaEquiv (squareTriangle 0 ≫ f)).obj ⟨ULift.up (2 : Fin 3)⟩) :=
  stableTriangleDiagonalMap (SSet.yonedaEquiv (squareTriangle 0 ≫ f))

/-- 概要：同じ対角完全射の全一単体は元四角形の共有対角そのもの。
方針：元対角辺の式と Yoneda の面制限式を使う。
規約：全単体の厳密等号。使われ方：零完全射の比較一意性の入力照合。 -/
lemma stableSquareDiagonalMap_diagram :
    SSet.yonedaEquiv.symm (stableArrow (stableSquareDiagonalMap f)).edge = squareDiagonal ≫ f := by
  apply SSet.yonedaEquiv.injective
  calc
    SSet.yonedaEquiv _ = (stableArrow (stableSquareDiagonalMap f)).edge :=
      Equiv.apply_symm_apply _ _
    _ = StableInfinity.{u}.δ (1 : Fin 3) (SSet.yonedaEquiv (squareTriangle 0 ≫ f)) :=
      stableTriangleDiagonalMap_edge _
    _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ (squareTriangle 0 ≫ f)) :=
      (stdSimplex.yonedaEquiv_δ_comp _ _).symm
    _ = SSet.yonedaEquiv (squareDiagonal ≫ f) := by
      rw [← Category.assoc, squareTriangle_diagonal]

/-- 概要：元上二単体の中間安定圏は元四角形の同じ零角。
方針：同じ標準中間頂点における元四角形の自然性を使う。
規約：元零角を保持。使われ方：元共有対角の全零性。 -/
lemma stableSquareUpperTriangle_middle :
    (SSet.yonedaEquiv (squareTriangle 0 ≫ f)).obj ⟨ULift.up (1 : Fin 3)⟩ =
      stableObject (squareVertex f 0 1) := by
  let t := SSet.yonedaEquiv (squareTriangle.{u + 1} 0)
  have hn := NatTrans.naturality_apply f
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (1 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (1 : Fin 3)).op t =
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    apply Prod.ext <;> apply SSet.stdSimplex.ext <;> intro i <;> fin_cases i <;> rfl
  have hn' := congrArg stableObject hn
  rw [hs] at hn'
  exact hn'.symm

/-- 概要：元零角を通る四角形の対角完全射は全零。
方針：元上二単体の中間対象を同じ零角へ照合して零対角補題を使う。
規約：元四角形・元対角を保持。使われ方：上下共有対角の比較一意性。 -/
lemma stableSquareDiagonalMap_zero (hz : IsZeroCategory (stableObject (squareVertex f 0 1)))
    (x : ((SSet.yonedaEquiv (squareTriangle 0 ≫ f)).obj ⟨ULift.up (0 : Fin 3)⟩).obj _⦋0⦌) :
    IsZeroVertex ((stableSquareDiagonalMap f).hom.app (Opposite.op ⦋0⦌) x) := by
  apply stableTriangleDiagonalMap_zero
  rw [stableSquareUpperTriangle_middle]
  exact hz
end SerrePositivity.KST.SConstruction
