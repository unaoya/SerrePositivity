module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.DerivedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeClosure
public import Mathlib.CategoryTheory.Shift.Induced
public import Mathlib.CategoryTheory.Shift.CommShift

/-! # Semifree 導来同値と整数シフト

概要：semifree 複体の H⁰ に通常の複体シフトを導入し、導来比較の整合性を示す。
方針：充満忠実なホモトピー比較を通じて零・加法の整合性を誘導する。
規約：対象のシフトは元の複体のシフト。使われ方：後の三角構造の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S]

/-- 概要：H⁰ の対象の元の semifree 複体を取り出す。
方針：射だけを商にした対象の包装を外す。規約：対象は同じ。
使われ方：通常の複体シフトの適用。 -/
abbrev semifreeHomotopyObject
    (X : DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S :=
  ForgetEnrichment.to (Complex S) X.as

/-- 概要：H⁰ の対象を元の複体でシフトする。
方針：シフト閉性を添えて対象に戻す。規約：整数シフト。
使われ方：H⁰ のシフト関手の対象成分。 -/
def semifreeShiftObject (s : ℤ)
    (X : DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) :
    DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :=
  (toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).obj (ForgetEnrichment.of (Complex S)
    (⟨(semifreeHomotopyObject S X).val⟦s⟧,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_shift S (semifreeHomotopyObject S X).property s⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S))

/-- 概要：シフトした対象のホモトピー比較は比較後のシフトと同型。
方針：通常のホモトピー商のシフト比較を適用する。規約：Mathlib の比較を継承。
使われ方：H⁰ 上のシフトされた射の定義。 -/
def semifreeShiftObjectIso (s : ℤ)
    (X : DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).obj (semifreeShiftObject S s X) ≅
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).obj X)⟦s⟧ :=
  ((_root_.HomotopyCategory.quotient (ModuleCat S) (.up ℤ)).commShiftIso s).app
    (semifreeHomotopyObject S X).val

/-- 概要：semifree 複体の H⁰ 上の整数シフト関手。
方針：通常のシフトされた射を充満忠実比較で引き戻す。
規約：対象は元の複体のシフト。使われ方：シフトの整合性の誘導。 -/
def semifreeShift (s : ℤ) :
    DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) ⥤
      DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) where
  obj := semifreeShiftObject S s
  map {X Y} f := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).preimage
    ((semifreeShiftObjectIso S s X).hom ≫
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map f)⟦s⟧') ≫ (semifreeShiftObjectIso S s Y).inv)
  map_id X := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map_injective
    rw [Functor.map_preimage, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map_id,
      (shiftFunctor (_root_.HomotopyCategory (ModuleCat S) (.up ℤ)) s).map_id,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map_id]
    simp only [Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map_injective
    simp only [Functor.map_preimage, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- 概要：明示的シフトとホモトピー比較の可換性。
方針：対象比較と射の定義を照合する。規約：自然同型として与える。
使われ方：零・加法の整合性を誘導する際のデータ。 -/
def semifreeShiftComparisonIso (s : ℤ) :
    semifreeShift S s ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S ⋙ shiftFunctor _ s :=
  NatIso.ofComponents (semifreeShiftObjectIso S s) (by
    intro X Y f
    simp only [Functor.comp_map, semifreeShift, Functor.map_preimage,
      Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- 概要：semifree 複体の H⁰ は通常の複体シフトを持つ。
方針：ホモトピー圏への充満忠実比較から整合性を誘導する。
規約：対象は元の複体のシフト。使われ方：導来比較のシフト整合性。 -/
instance semifreeHomotopyHasShift :
    HasShift (DifferentialGraded.HomotopyCategory S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)) ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S)).hasShift
    (semifreeShift S) (semifreeShiftComparisonIso S)

/-- 概要：ホモトピー比較は整数シフトと整合する。
方針：誘導したシフトの標準比較を用いる。規約：零と加法の整合性も含む。
使われ方：導来圏への比較との合成。 -/
instance semifreeHomotopyComparisonCommShift : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S))
    (semifreeShift S) (semifreeShiftComparisonIso S)

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：semifree 導来比較は整数シフトと整合する。
方針：ホモトピー比較と Mathlib の `Qh` の整合性を合成する。
規約：導来圏の選択以外の仮定はない。使われ方：三角構造の比較。 -/
instance semifreeDerivedComparisonCommShift : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedComparison S).CommShift ℤ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedComparison
  infer_instance

/-- 概要：semifree 導来同値の順関手は整数シフトと整合する。
方針：順関手は検証済みの比較関手そのもの。
規約：零・加法の coherence を含む。使われ方：導来同値の三角関手化。 -/
instance semifreeDerivedEquivalenceCommShift :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeDerivedEquivalence S).functor.CommShift ℤ :=
  semifreeDerivedComparisonCommShift S

end SerrePositivity.InfinityCategories.Project.DerivedCategories
