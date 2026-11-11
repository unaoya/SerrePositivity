module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor

/-!
概要：反復 curry の内部 Hom 同型を、元の射の単位頂点で計算する。
方針：二度 uncurry し、右単位子と結合子の coherence を使う。
規約：一般の閉モノイダル圏。使われ方：全パラメータの構造可換式の成分の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomTensor
end SerrePositivity.KST.Spectra.InternalHomTensor
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorVertices
open _root_.SerrePositivity.KST.Spectra.InternalHomTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 反復内部 Hom の同型は、元の射の curry の単位頂点を厳密に表す。 -/
lemma curry'_hom {K A V : C} (f : K ⊗ A ⟶ V) :
    curry' f ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso K A V).hom = curry' (curry f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.hom_eq]
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_curry]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, curry', uncurry_curry]
  conv_rhs => rw [curry', uncurry_curry, uncurry_natural_left, uncurry_curry]
  rw [← Category.assoc]
  congr 1
  monoidal

end SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorVertices

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomTensor.curry'_hom := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorVertices.curry'_hom
