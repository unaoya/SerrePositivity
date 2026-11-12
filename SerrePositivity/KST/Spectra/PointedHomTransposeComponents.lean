module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：二つの点つき Hom の源を転置し、元の全パラメータの成分を保持する。
方針：内部 Hom 交換を単位頂点で評価し、二度の転置を対称性で消去する。
規約：Kan 性不要。使われ方：パラメータ付きの列の厳密化の前後の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 全パラメータの点つき写像族の二つの源を交換する。 -/
def transpose {A U V : PointedSimplicialSet.{u}}
    (f : A ⟶ (ihom U).obj V) : U ⟶ (ihom A).obj V :=
  curry ((β_ A U).hom ≫ uncurry f)

/-- 全パラメータの転置を二度施すと元の族そのものへ戻る。 -/
lemma transpose_transpose {A U V : PointedSimplicialSet.{u}}
    (f : A ⟶ (ihom U).obj V) : transpose (transpose f) = f := by
  unfold transpose
  rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
    curry_uncurry]

/-- 元の族の転置の頂点は、元の内部 Hom 交換の同じ頂点。 -/
lemma familyVertex_transpose {A U V : PointedSimplicialSet.{u}}
    (f : A ⟶ (ihom U).obj V) :
    familyVertex (transpose f) =
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right.app (Opposite.op ⦋0⦌) (familyVertex f) := by
  have h := congrArg (PointedSimplicialSet.unitVertexEquiv _)
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom f)
  rw [PointedSimplicialSet.unitVertexEquiv_naturality] at h
  exact (familyVertex_eq_pointedHomVertex _).trans
    (h.symm.trans (congrArg _ (familyVertex_eq_pointedHomVertex _).symm))

/-- 同じ全パラメータの成分を持つ二つの族は、転置後も同じ成分を持つ。 -/
lemma componentOf_transpose {A U V : PointedSimplicialSet.{u}}
    {f g : A ⟶ (ihom U).obj V} (h : componentOf f = componentOf g) :
    componentOf (transpose f) = componentOf (transpose g) := by
  have he := congrArg (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A U V).hom.right) h
  simpa only [componentOf, mapπ₀_mk, familyVertex_transpose] using he

end SerrePositivity.KST.Spectra.PointedMapping
