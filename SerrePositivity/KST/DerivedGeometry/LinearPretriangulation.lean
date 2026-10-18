module

public import SerrePositivity.KST.DerivedGeometry.LinearRepresentableClosure
public import SerrePositivity.KST.DerivedGeometry.DGResolution.YonedaTria

/-!
概要：一般の線形加法圏の複体 dg 圏の H⁰ と有限 cell の前三角化を比較する。
方針：操作木による代表可能性と、実際の導来 Yoneda の完全忠実性を組み合わせる。
規約：冪等完備化を行わず、別々の圏の間の同値を証明する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の層複体の増強の比較。
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
variable [Small.{u} (CochainComplex C ℤ)] [HasZeroObject C] [HasBinaryBiproducts C]

/--
概要：複体 dg 圏の H⁰ から tria への Yoneda は本質的全射。
方針：有限 cell の代表可能性の証明を一般の本質的全射性の判定に渡す。
規約：代表可能性を未証明の入力にしない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化。
-/
instance complexYonedaToTria_essSurj :
    (DGResolution.yonedaToTria A (CochainComplex C ℤ)).EssSurj := by
  apply DGResolution.yonedaToTria_essSurj_of_representable
  intro M hM
  obtain ⟨c⟩ := hM
  exact finiteCell_representable A c

/--
概要：複体 dg 圏の H⁰ から tria への実際の Yoneda は圏同値。
方針：完全忠実性と操作木の帰納による本質的全射性を束ねる。
規約：商 dg 圏の H⁰ との同値は別途証明する。
使われ方：Drinfeld §2.4、KST D4 の導来局所化との比較。
-/
instance complexYonedaToTria_isEquivalence :
    (DGResolution.yonedaToTria A (CochainComplex C ℤ)).IsEquivalence where

/--
概要：元の複体 dg 圏の H⁰ と前三角化との同値。
方針：証明済みの実際の Yoneda 関手の同値性を使う。
規約：対象を定義で同一視せず、商の H⁰ の比較とも区別する。
使われ方：Drinfeld §2.4、KST D4・§10-7 の Mathlib 導来圏との比較の前段階。
-/
def homotopyTriaEquivalence :
    HomotopyCategory A (CochainComplex C ℤ) ≌ TriaCategory A (CochainComplex C ℤ) :=
  (DGResolution.yonedaToTria A (CochainComplex C ℤ)).asEquivalence

end SerrePositivity.KST.DerivedGeometry.LinearComplex
