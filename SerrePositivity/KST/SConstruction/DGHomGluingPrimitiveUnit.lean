module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.PrimitiveComparison

/-! # 元の gluing 単位の第三成分
概要：元の閉単位の比較 cochain の零性を、同じ実単位元の値に戻す。
方針：元の単位複体の 1 と cochain の評価を使う。
規約：元の gluing の単位を保持。使われ方：実 cone 関手の単位保存。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の実 gluing 単位の第三成分は零。 -/
lemma dgHomGluingUnit_primitive (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X X).v 0 (-1) (by omega)
      (unitElement R X).val = 0 := by
  have h := Cochain.congr_v (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity_comparison R C D M X)
    0 (-1) (by omega)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.zero_v] at h
  exact congrArg (fun f => f
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat R))).inv 1)) h

end SerrePositivity.KST.SConstruction
