module

public import SerrePositivity.KST.DerivedGeometry.LinearRepresentableTriangles
public import SerrePositivity.KST.DerivedGeometry.LinearYonedaHomotopy
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-!
概要：元の複体の Mathlib ホモトピー圏からの代表加群関手の完全性を証明する。
方針：shift と標準 cone 三角形の比較を、商の因子分解の正方形で降ろす。
規約：元の Mathlib の distinguished triangle を使う。
使われ方：Drinfeld §2.4、KST D4・§10-7 の acyclic 局所化との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits Pretriangulated
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)] [HasBinaryBiproducts C]

/--
概要：元のホモトピー圏の標準 cone 三角形は代表加群の標準三角形へ送られる。
方針：複体の段階の三角形の同型を、shift と整合する商の正方形で降ろす。
規約：同じ標準 cone と比較同型を使う。
使われ方：Drinfeld §2.4、KST D4 の distinguished triangle の保存。
-/
def nativeHomotopyYonedaConeTriangleIso {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    (nativeHomotopyYoneda A).mapTriangle.obj (CochainComplex.mappingCone.triangleh f) ≅
      moduleHomotopyConeTriangle A (CochainComplex C ℤ) (representablePostcompose A f) :=
  mapTriangleSquareIso (_root_.HomotopyCategory.quotient C (.up ℤ))
    (nativeHomotopyYoneda A) (complexYoneda A) (moduleToHomotopy A (CochainComplex C ℤ))
    (nativeHomotopyYonedaFacIso A) (CochainComplex.mappingCone.triangle f)
    (moduleConeTriangle A (CochainComplex C ℤ) (representablePostcompose A f))
    (complexYonedaConeTriangleIso A f).symm

/--
概要：Mathlib ホモトピー圏からの実際の代表加群関手は distinguished triangle を保つ。
方針：全ての distinguished triangle の標準 cone 表示に構成した三角形の同型を適用する。
規約：対象の同値から三角構造を新しく定義することはしない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の導来局所化との比較。
-/
instance nativeHomotopyYoneda_isTriangulated [HasZeroObject C] :
    (nativeHomotopyYoneda (C := C) A).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨X, Y, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _
      (moduleHomotopyConeTriangle_distinguished A (CochainComplex C ℤ)
        (representablePostcompose A f)) _
      ((nativeHomotopyYoneda A).mapTriangle.mapIso e ≪≫ nativeHomotopyYonedaConeTriangleIso A f)

end SerrePositivity.KST.DerivedGeometry.LinearComplex
