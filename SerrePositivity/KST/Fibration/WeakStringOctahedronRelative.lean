module
public import SerrePositivity.KST.Fibration.WeakStringOctahedronExact
public import SerrePositivity.KST.Fibration.CofiberFamilyKernelRestriction

/-! # 核の相対 cofiber 図式に値を持つ八面体比較関手

実八面体の最後の列を E(ker q,B,ker q) の完全関手に制限する。
包含は元の実四角形の全族を回収し、両端の核値評価も完全関手として保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の八面体比較列の、両端が核に入る全相対四角形の族。 -/
def weakStringOctahedronRelativeFamily {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringCategory q n ⟶
      relativeCofiberDiagrams (kernelClosedPredicate q) (kernelClosedPredicate q) :=
  cofiberFamilyKernelRestriction q (weakStringOctahedronFamily q β).second.rightZeroTriangle
    (weakStringOctahedronFamily q β).second.right_isCofiber
    (weakStringOctahedronFamily_source_kernel q β) (weakStringOctahedronFamily_target_kernel q β)

/-- 相対制限は元の全四角形の族を厳密に回収する。 -/
lemma weakStringOctahedronRelativeFamily_ι {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringOctahedronRelativeFamily q β ≫
      (relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q)).val =
        weakStringOctahedronCofiberFamily q β := rfl

/-- 両端が核に入る元の八面体の比較列は、相対図式値の完全関手を与える。 -/
def weakStringOctahedronRelativeExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringModel q n ⟶
      relativeCofiberStableModel (kernelClosedPredicate q) (kernelClosedPredicate q) :=
  ⟨weakStringOctahedronRelativeFamily q β, by
    apply preservesCofiberData_fullSubcomplex_of_comp
      (relativeCofiberPredicate (kernelClosedPredicate q) (kernelClosedPredicate q)).predicate
    change PreservesCofiberData (weakStringOctahedronRelativeFamily q β ≫
      (relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q)).val)
    rw [weakStringOctahedronRelativeFamily_ι]
    exact weakStringOctahedronCofiberFamily_preservesCofiberData q β⟩

/-- 完全関手としても、相対制限は元の実八面体の全四角形を厳密に保つ。 -/
lemma weakStringOctahedronRelativeExact_inclusion {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringOctahedronRelativeExact q β ≫
      relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q) =
        weakStringOctahedronCofiberExact q β := Subtype.ext rfl

/-- 元の比較列の始点を取る、核に値を持つ完全関手。 -/
def weakStringOctahedronSourceExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringModel q n ⟶ closedStableModel (kernelClosedPredicate q) :=
  weakStringOctahedronRelativeExact q β ≫
    relativeCofiberSubobject (kernelClosedPredicate q) (kernelClosedPredicate q)

/-- 元の比較列の cofiber を取る、核に値を持つ完全関手。 -/
def weakStringOctahedronTargetExact {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) :
    weakStringModel q n ⟶ closedStableModel (kernelClosedPredicate q) :=
  weakStringOctahedronRelativeExact q β ≫
    relativeCofiberQuotient (kernelClosedPredicate q) (kernelClosedPredicate q)

end SerrePositivity.KST.Fibration
