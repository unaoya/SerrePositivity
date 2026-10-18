module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.Quotient

/-!
# 分解前後の指定対象の三角閉包

概要：準同値の前三角化比較で、指定代表加群の三角閉包を対応させる。
方針：代表加群の比較、三角閉包の最小性、導来随伴の単位を使う。
規約：台を持つ部分圏の一致を未証明の構造フィールドに置かない。
使われ方：Drinfeld Thm 3.4・§3.5、KST D4 の指定 Verdier 商の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F

/--
概要：導来延長は指定代表対象の三角閉包をその像の閉包へ送る。
方針：代表加群の比較と逆像部分圏の三角性を使う。
規約：対象集合の像の包含だけで十分。
使われ方：Drinfeld Thm 3.4・§3.5 の指定部分圏の比較。
-/
theorem extension_supportedFiniteCell (S : Set D) (T : Set E)
    (hST : ∀ d ∈ S, F.obj d ∈ T) {X : DerivedModuleCategory A D}
    (hX : derivedFiniteCellOver A D S X) :
    derivedFiniteCellOver A E T ((dgDerivedExtension A D E F).obj X) := by
  let P := (derivedFiniteCellOver A E T).inverseImage (dgDerivedExtension A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((derivedFiniteCellOver_le_iff_generators A D P S).2 ?_) X hX
  intro d hd
  exact (derivedFiniteCellOver A E T).prop_of_iso
    (dgDerivedExtensionRepresentableIso A D E F d).symm
    ((moduleFiniteCellOver A E T).prop_map_obj (moduleToDerived A E)
      (moduleFiniteCellOver_representable A E (F.obj d) (hST d hd)))

/--
概要：指定対象が持ち上がる準同値の導来制限は指定三角閉包を保つ。
方針：持ち上げた代表加群の比較を導来随伴の単位と合成する。
規約：任意の対象集合に持ち上げ可能性を自動では仮定しない。
使われ方：Drinfeld §3.5、KST D4 の増大関手の逆向きの比較。
-/
theorem restriction_supportedFiniteCell (hF : QuasiEquivalence F) (S : Set D) (T : Set E)
    (hTS : ∀ e ∈ T, ∃ d ∈ S, F.obj d = e) {X : DerivedModuleCategory A E}
    (hX : derivedFiniteCellOver A E T X) :
    derivedFiniteCellOver A D S ((dgDerivedRestriction A D E F).obj X) := by
  let P := (derivedFiniteCellOver A D S).inverseImage (dgDerivedRestriction A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((derivedFiniteCellOver_le_iff_generators A E P T).2 ?_) X hX
  intro e he
  obtain ⟨d, hd, rfl⟩ := hTS e he
  exact (derivedFiniteCellOver A D S).prop_of_iso
    ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app _ ≪≫
      (dgDerivedRestriction A D E F).mapIso (dgDerivedExtensionRepresentableIso A D E F d))
    ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCellOver_representable A D d hd))

/--
概要：指定対象を全射的に対応させる準同値は指定三角閉包の所属条件を同定する。
方針：延長と制限の保存性、および導来同値の単位を使う。
規約：retract を追加しない。
使われ方：Drinfeld Thm 3.4・§3.5 の指定 Verdier 商の移送。
-/
theorem extension_supportedFiniteCell_iff (hF : QuasiEquivalence F) (S : Set D) (T : Set E)
    (hST : ∀ d ∈ S, F.obj d ∈ T) (hTS : ∀ e ∈ T, ∃ d ∈ S, F.obj d = e)
    (X : DerivedModuleCategory A D) :
    derivedFiniteCellOver A E T ((dgDerivedExtension A D E F).obj X) ↔
      derivedFiniteCellOver A D S X := by
  constructor
  · intro hX
    exact (derivedFiniteCellOver A D S).prop_of_iso
      ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app X).symm
      (restriction_supportedFiniteCell A D E F hF S T hTS hX)
  · exact extension_supportedFiniteCell A D E F S T hST

omit E [DGCategory A E] [Small.{u} E] F in
/--
概要：増大準同値の前三角化比較は指定対象の閉包を元の閉包へ同定する。
方針：対象ラベルの具体的な同値で指定対象の持ち上げを作る。
規約：指定対象集合に同型閉性を要求しない。
使われ方：Drinfeld §3.5、KST D4 の分解前後の Verdier 商。
-/
theorem augmentation_triaImage_iff (N : Set D) (X : TriaCategory A (Objects A D)) :
    triaImage A D N ((triaExtension A (Objects A D) D (augmentation A D)).obj X) ↔
      triaImage A (Objects A D) (nullObjects A D N) X := by
  exact extension_supportedFiniteCell_iff A (Objects A D) D (augmentation A D)
    (augmentation_quasiEquivalence A D) (nullObjects A D N) N (fun _ hx => hx)
    (fun d hd => ⟨objectEquiv A D d, hd, rfl⟩) X.obj

end SerrePositivity.KST.DerivedGeometry.DGResolution
