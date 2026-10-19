module
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation

/-! # Slice の四角形表示と固定 cospan

概要：slice からの四角形図式は右・上辺を固定し、終点評価が定値となる。
方針：普遍錐の固定条件と形状同型の逆則を使う。
規約：値域に追加仮定なし。使われ方：D7 の前合成比較の終点成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- 全錐の図式表示を固定図式へ制限すると定値になる。 -/
lemma sliceConeDiagramMap_restriction {K X : SSet.{u}} (p : K ⟶ X) :
    sliceConeDiagramMap p ≫ coneRestriction K X = SSet.const (functorVertex p) := by
  change curry (sliceConeFamilyUncurry p) ≫ coneRestriction K X = _
  exact sliceConeFamilyUncurry_curry_fixed p

/-- 四角形表示の cospan への制限は全錐図式の制限と同じ。 -/
lemma sliceSquareDiagramMap_restriction {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    sliceSquareDiagramMap p ≫ (pre cospanSquareBoundary).app X =
      sliceConeDiagramMap p ≫ coneRestriction (horn 2 2 : SSet.{u}) X := by
  unfold sliceSquareDiagramMap coneRestriction
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  congr 2
  simp only [cospanSquareBoundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Slice の四角形表示は元の cospan を固定する。 -/
lemma sliceSquareDiagramMap_fixed {X : SSet.{u}} (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    sliceSquareDiagramMap p ≫ (pre cospanSquareBoundary).app X =
      SSet.const (functorVertex p) := by
  rw [sliceSquareDiagramMap_restriction, sliceConeDiagramMap_restriction]

/-- Cospan の共通終点の指定頂点。 -/
def cospanTargetVertex : (horn 2 2 : SSet.{u}) _⦋0⦌ :=
  horn₂₂.ι₀₂.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- Cospan の終点は正方形の終点へ写る。 -/
lemma cospanSquareBoundary_targetVertex :
    cospanSquareBoundary.app (Opposite.op ⦋0⦌) cospanTargetVertex =
      squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1 := by
  have h := congrArg (fun q => q.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) cospanSquareBoundary_rightEdge.{u}
  exact h.trans (by apply Prod.ext <;> decide)

/-- Slice の四角形表示の終点評価は cospan の共通終点に定値。 -/
lemma sliceSquareDiagramMap_targetEvaluation {X : SSet.{u}}
    (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    sliceSquareDiagramMap p ≫ evaluateFunctorAt (Y := X)
      (squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1) =
      SSet.const (p.app (Opposite.op ⦋0⦌) cospanTargetVertex) := by
  have he := stable_pre_evaluateFunctorAt (X := X) cospanSquareBoundary cospanTargetVertex
  rw [cospanSquareBoundary_targetVertex] at he
  rw [← he, ← Category.assoc, sliceSquareDiagramMap_fixed, SSet.const_comp,
    evaluateFunctorAt_functorVertex]

end SerrePositivity.InfinityCategories
