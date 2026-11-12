module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorAction
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor

/-!
概要：テンソル作用の Hom 写像は、構造射の随伴への後合成と一致する。
方針：二重 uncurry で評価射の自然性と結合子の相殺に帰着する。
規約：一般の閉モノイダル圏で証明する。使われ方：Ω 条件の写像空間への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]

/-- テンソルした射を構造射と合成し curry すると、その随伴への後合成になる。 -/
lemma tensorHom_adjoint (S A B Z : C) (s : S ⊗ B ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom S A B ≫ (ihom (S ⊗ A)).map s ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso S A Z).hom =
      (ihom A).map (curry s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.hom_eq]
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_curry, uncurry_ihom_map]
  rw [← Category.assoc, ← Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
  rw [associator_inv_naturality_right, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← uncurry_eq, uncurry_ihom_map, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom_evaluation_assoc,
    Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.tensorHom_adjoint := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom_adjoint
