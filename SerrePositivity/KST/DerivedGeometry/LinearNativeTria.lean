module

public import SerrePositivity.KST.DerivedGeometry.LinearNativeComparison
public import SerrePositivity.KST.DerivedGeometry.LinearYonedaTriangulated
public import SerrePositivity.DifferentialGraded.Verdier.Derived

/-!
概要：元の Mathlib ホモトピー圏と代表加群の前三角化を三角同値で比較する。
方針：導来 Yoneda の完全忠実性、有限 cell の代表可能性、標準三角形の保存を使う。
規約：冪等完備化を加えず、既存の二つの三角構造を比較する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の acyclic 局所化と Mathlib 導来圏。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：元の複体の導来 Yoneda 像は同じ複体の代表加群の導来像と同型。
方針：ホモトピー商の比較と既存の導来局所化の比較を合成する。
規約：元の chain complex を取り替えない。
使われ方：Drinfeld §2.4、KST D4 の代表対象の計算。
-/
def nativeDerivedYoneda_objIso (X : CochainComplex C ℤ) :
    (nativeDerivedYoneda A).obj ((_root_.HomotopyCategory.quotient C (.up ℤ)).obj X) ≅
      (moduleToDerived A (CochainComplex C ℤ)).obj ((complexYoneda A).obj X) :=
  (moduleHomotopyToDerivedClosed A (CochainComplex C ℤ)).mapIso
    ((nativeHomotopyYonedaFacIso A).app X) ≪≫
      (moduleToHomotopyDerivedIso A (CochainComplex C ℤ)).app ((complexYoneda A).obj X)

/--
概要：元のホモトピー圏からの導来 Yoneda の全対象は有限 cell の導来像に属する。
方針：代表対象での計算同型と代表加群の有限 cell 性を使う。
規約：追加の retract は使わない。
使われ方：Drinfeld §2.4、KST D4 の tria への制限。
-/
theorem nativeDerivedYoneda_mem (X : _root_.HomotopyCategory C (.up ℤ)) :
    derivedFiniteCellOver A (CochainComplex C ℤ) Set.univ ((nativeDerivedYoneda A).obj X) := by
  obtain ⟨X⟩ := X
  exact (derivedFiniteCellOver A (CochainComplex C ℤ) Set.univ).prop_of_iso
    (nativeDerivedYoneda_objIso A X).symm
    ((moduleFiniteCellOver A (CochainComplex C ℤ) Set.univ).prop_map_obj
      (moduleToDerived A (CochainComplex C ℤ)) (moduleFiniteCell_representable A _ X))

/--
概要：元の Mathlib ホモトピー圏から tria への実際の導来 Yoneda 関手。
方針：有限 cell の像に属する証明を使って充満部分圏へ制限する。
規約：商の H⁰ の関手とは区別する。
使われ方：Drinfeld §2.4、KST D4 の acyclic 局所化の比較。
-/
def nativeToTria : _root_.HomotopyCategory C (.up ℤ) ⥤ TriaCategory A (CochainComplex C ℤ) :=
  (derivedFiniteCellOver A (CochainComplex C ℤ) Set.univ).lift (nativeDerivedYoneda A)
    (nativeDerivedYoneda_mem A)

/--
概要：元のホモトピー圏から tria への関手は充満。
方針：証明済みの実際の導来 Yoneda の充満性を制限する。
規約：三角閉包の構成を変更しない。
使われ方：Drinfeld §2.4、KST D4 の tria 同値。
-/
instance nativeToTria_full : (nativeToTria (C := C) A).Full := by
  dsimp [nativeToTria]; infer_instance

/--
概要：元のホモトピー圏から tria への関手は忠実。
方針：証明済みの実際の導来 Yoneda の忠実性を制限する。
規約：元の射の等式を反映する。
使われ方：Drinfeld §2.4、KST D4 の tria 同値。
-/
instance nativeToTria_faithful : (nativeToTria (C := C) A).Faithful := by
  dsimp [nativeToTria]; infer_instance

variable [HasZeroObject C] [HasBinaryBiproducts C]

/--
概要：元のホモトピー圏から tria への関手は本質的全射。
方針：有限 cell の操作木の代表可能性と対象計算同型を使う。
規約：存在を未証明のフィールドとして仮定しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の同定。
-/
instance nativeToTria_essSurj : (nativeToTria (C := C) A).EssSurj where
  mem_essImage X := by
    obtain ⟨M, ⟨c⟩, ⟨e⟩⟩ := X.property
    obtain ⟨Y, ⟨ey⟩⟩ := finiteCell_representable A c
    refine ⟨(_root_.HomotopyCategory.quotient C (.up ℤ)).obj Y, ⟨?_⟩⟩
    exact (derivedFiniteCellOver A (CochainComplex C ℤ) Set.univ).isoMk
      (nativeDerivedYoneda_objIso A Y ≪≫ (moduleToDerived A (CochainComplex C ℤ)).mapIso ey.symm ≪≫ e)

/--
概要：元のホモトピー圏と tria の比較関手は圏同値。
方針：完全忠実性と操作木の帰納による本質的全射性を束ねる。
規約：同じ代表加群関手を使う。
使われ方：Drinfeld §2.4、KST D4 の局所化の移送。
-/
instance nativeToTria_isEquivalence : (nativeToTria (C := C) A).IsEquivalence where

/--
概要：元のホモトピー圏から tria の比較関手は shift と整合的に可換。
方針：構成済みのホモトピー Yoneda と導来局所化の shift 構造を制限する。
規約：標準の shift を変更しない。
使われ方：Drinfeld §2.4、KST D4 の三角同値。
-/
instance nativeToTria_commShift : (nativeToTria (C := C) A).CommShift ℤ := by
  dsimp [nativeToTria, nativeDerivedYoneda]; infer_instance

/--
概要：元のホモトピー圏から tria の比較関手は distinguished triangle を保つ。
方針：標準 cone 三角形による保存の証明と導来局所化の完全性を合成する。
規約：両辺の既存の三角構造を使う。
使われ方：Drinfeld §2.4、KST D4・§10-7 の acyclic 局所化。
-/
instance nativeToTria_isTriangulated : (nativeToTria (C := C) A).IsTriangulated := by
  dsimp [nativeToTria, nativeDerivedYoneda]; infer_instance

/--
概要：Mathlib ホモトピー圏と代表加群の前三角化との圏同値。
方針：同じ導来 Yoneda の完全忠実性と本質的全射性の証明を使う。
規約：冪等完備化は行わない。
使われ方：Drinfeld §2.4、KST D4 の acyclic 局所化の移送。
-/
def nativeTriaEquivalence : _root_.HomotopyCategory C (.up ℤ) ≌
    TriaCategory A (CochainComplex C ℤ) := (nativeToTria A).asEquivalence

/--
概要：ホモトピー圏と tria の同値の順関手の shift 構造。
方針：構成済みの比較関手の構造を保持する。
規約：shift を取り替えない。
使われ方：Drinfeld §2.4、KST D4 の三角同値。
-/
instance nativeTriaEquivalence_functorCommShift :
    (nativeTriaEquivalence (C := C) A).functor.CommShift ℤ := nativeToTria_commShift A

/--
概要：ホモトピー圏と tria の同値の逆関手の shift 構造。
方針：順関手の構造から随伴の整合性を持つ逆構造を得る。
規約：順逆の構造を独立に選ばない。
使われ方：Drinfeld §2.4、KST D4 の三角同値。
-/
instance nativeTriaEquivalence_inverseCommShift :
    (nativeTriaEquivalence (C := C) A).inverse.CommShift ℤ :=
  (nativeTriaEquivalence A).commShiftInverse ℤ

/--
概要：ホモトピー圏と tria の同値の随伴全体は shift と整合的。
方針：順関手の可換性から単位・余単位の互換性を得る。
規約：同じ同値を使う。
使われ方：Drinfeld §2.4、KST D4 の局所化の比較。
-/
instance nativeTriaEquivalence_commShift : (nativeTriaEquivalence (C := C) A).CommShift ℤ :=
  (nativeTriaEquivalence A).commShift_of_functor ℤ

/--
概要：Mathlib ホモトピー圏と tria の同値は三角同値。
方針：標準 cone の保存から得た同じ順関手の完全性を使う。
規約：既存の三角構造を比較する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の Mathlib 導来局所化。
-/
instance nativeTriaEquivalence_isTriangulated :
    (nativeTriaEquivalence (C := C) A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (nativeToTria_isTriangulated A)

end SerrePositivity.KST.DerivedGeometry.LinearComplex
