module

public import SerrePositivity.KST.DerivedGeometry.LinearYonedaHomotopy
public import SerrePositivity.KST.DerivedGeometry.DGResolution.DerivedYoneda

/-!
概要：元の Mathlib ホモトピー圏からの代表加群の導来関手を実際の dg Yoneda と比較する。
方針：二つのホモトピー商の比較正方形を等式で固定し、完全忠実性を移す。
規約：三角構造を定義で移し替えない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の acyclic 局所化の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：閉零射の比較を通した具体的な代表加群関手は実際の dg Yoneda に一致する。
方針：各 Hom の閉零射の同値と後合成の比較を使う。
規約：対象も射も同じ関手として照合する。
使われ方：Drinfeld §2.4、KST D4 の比較正方形。
-/
theorem closedYoneda_fac :
    closedToComplex (C := C) A ⋙ complexYoneda A =
      (dgYoneda A (CochainComplex C ℤ)).onClosed := by
  apply CategoryTheory.Functor.ext
  swap
  · intro X; rfl
  · intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change representablePostcompose A (closedHomEquiv A X Y f) = _
    rw [representablePostcompose_eq_yoneda, Equiv.symm_apply_apply]

/--
概要：H⁰ の比較を通したホモトピー圏の代表加群関手は dg Yoneda の H⁰ 関手に一致する。
方針：合同関係による商の一意性と閉零の比較正方形を使う。
規約：同じ quotient functor を使う。
使われ方：Drinfeld §2.4、KST D4 の完全忠実性の移送。
-/
theorem nativeHomotopyYoneda_square :
    homotopyComparison (C := C) A ⋙ nativeHomotopyYoneda A =
      (dgYoneda A (CochainComplex C ℤ)).onHomotopy := by
  apply CategoryTheory.Quotient.lift_unique'
  change toHomotopy A (CochainComplex C ℤ) ⋙
      (homotopyComparison A ⋙ nativeHomotopyYoneda A) =
    toHomotopy A (CochainComplex C ℤ) ⋙ (dgYoneda A (CochainComplex C ℤ)).onHomotopy
  rw [← CategoryTheory.Functor.assoc, homotopyComparison_fac,
    CategoryTheory.Functor.assoc]
  have hn : _root_.HomotopyCategory.quotient C (.up ℤ) ⋙ nativeHomotopyYoneda A =
      complexYoneda A ⋙ moduleToHomotopy A (CochainComplex C ℤ) :=
    CategoryTheory.Quotient.lift_spec _ _ _
  rw [hn, ← CategoryTheory.Functor.assoc, closedYoneda_fac, DGFunctor.onHomotopy_fac]

/--
概要：元の Mathlib ホモトピー圏から実際の導来 dg 加群圏への代表加群関手。
方針：具体的なホモトピー圏の関手と既存の導来局所化を合成する。
規約：新しい導来圏は構成しない。
使われ方：Drinfeld §2.4、KST D4 の tria と acyclic 局所化の比較。
-/
def nativeDerivedYoneda : _root_.HomotopyCategory C (.up ℤ) ⥤
    DerivedModuleCategory A (CochainComplex C ℤ) :=
  nativeHomotopyYoneda A ⋙ moduleHomotopyToDerivedClosed A (CochainComplex C ℤ)

/--
概要：二つのホモトピー圏の比較は同じ導来 Yoneda の正方形を与える。
方針：ホモトピー圏の比較正方形に導来局所化を合成する。
規約：射の局所化を変更しない。
使われ方：Drinfeld §2.4、KST D4 の完全忠実性の移送。
-/
theorem nativeDerivedYoneda_square :
    homotopyComparison (C := C) A ⋙ nativeDerivedYoneda A =
      representableHomotopyToDerived A (CochainComplex C ℤ) := by
  rw [nativeDerivedYoneda, ← CategoryTheory.Functor.assoc, nativeHomotopyYoneda_square]
  rfl

/--
概要：元のホモトピー圏から実際の導来加群圏への代表加群関手は充満。
方針：H⁰ の同値を前合成した導来 Yoneda の充満性を使う。
規約：非有界の全複体を扱う。
使われ方：Drinfeld §2.4、KST D4 の tria 同値。
-/
instance nativeDerivedYoneda_full : (nativeDerivedYoneda (C := C) A).Full := by
  let : (homotopyComparison (C := C) A ⋙ nativeDerivedYoneda A).Full :=
    (nativeDerivedYoneda_square (C := C) A).symm ▸
      DGResolution.derivedYoneda_full A (CochainComplex C ℤ)
  apply (nativeDerivedYoneda A).full_of_comp_essSurj (homotopyComparison A)
  intro X Y f
  obtain ⟨g, hg⟩ := (homotopyComparison A ⋙ nativeDerivedYoneda A).map_surjective f
  exact ⟨(homotopyComparison A).map g, hg⟩

/--
概要：元のホモトピー圏から実際の導来加群圏への代表加群関手は忠実。
方針：H⁰ の同値を前合成した導来 Yoneda の忠実性を使う。
規約：元のホモトピー圏の射の等式を反映する。
使われ方：Drinfeld §2.4、KST D4 の tria 同値。
-/
instance nativeDerivedYoneda_faithful : (nativeDerivedYoneda (C := C) A).Faithful := by
  let : (homotopyComparison (C := C) A ⋙ nativeDerivedYoneda A).Faithful :=
    (nativeDerivedYoneda_square (C := C) A).symm ▸
      DGResolution.derivedYoneda_faithful A (CochainComplex C ℤ)
  apply (nativeDerivedYoneda A).faithful_of_comp_essSurj (homotopyComparison A)
  intro X Y f g h
  obtain ⟨f', rfl⟩ := (homotopyComparison A).map_surjective f
  obtain ⟨g', rfl⟩ := (homotopyComparison A).map_surjective g
  exact congrArg (homotopyComparison A).map
    ((homotopyComparison A ⋙ nativeDerivedYoneda A).map_injective h)

end SerrePositivity.KST.DerivedGeometry.LinearComplex
