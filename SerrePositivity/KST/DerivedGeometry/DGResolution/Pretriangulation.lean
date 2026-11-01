module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.Surjectivity
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Verdier.Derived

/-!
# 準同値による前三角化の比較

概要：一般の dg 準同値による導来延長・制限を、有限 cell の三角閉包へ制限する。
方針：代表加群の比較、有限 cell の最小性、既存の導来随伴を使う。
規約：retract を追加せず tria を比較する。Dqc や Perf の増強にはまだ適用しない。
使われ方：Drinfeld §2.4・Lemma 13.5、KST D4 の分解の移送。
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
概要：dg 関手の導来延長は有限 cell の三角閉包を保つ。
方針：逆像が三角部分圏であることと代表加群の比較を使う。
規約：準同値性はこの向きには不要。
使われ方：Drinfeld §2.4 の前三角化の関手性。
-/
theorem extension_finiteCell {X : DerivedModuleCategory A D}
    (hX : derivedFiniteCellOver A D Set.univ X) :
    derivedFiniteCellOver A E Set.univ ((dgDerivedExtension A D E F).obj X) := by
  let P := (derivedFiniteCellOver A E Set.univ).inverseImage (dgDerivedExtension A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((derivedFiniteCellOver_le_iff_generators A D P Set.univ).2 ?_) X hX
  intro d _
  exact (derivedFiniteCellOver A E Set.univ).prop_of_iso
    (dgDerivedExtensionRepresentableIso A D E F d).symm
    (triaRepresentable A E (F.obj d)).property

/--
概要：準同値の導来制限は有限 cell の三角閉包を保つ。
方針：代表加群の本質的全射性と導来同値の単位を使う。
規約：有限 cell の閉包へ retract は追加しない。
使われ方：Drinfeld §2.4・Lemma 13.5 の前三角化の移送。
-/
theorem restriction_finiteCell (hF : QuasiEquivalence F) {X : DerivedModuleCategory A E}
    (hX : derivedFiniteCellOver A E Set.univ X) :
    derivedFiniteCellOver A D Set.univ ((dgDerivedRestriction A D E F).obj X) := by
  let P := (derivedFiniteCellOver A D Set.univ).inverseImage (dgDerivedRestriction A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  apply ((derivedFiniteCellOver_le_iff_generators A E P Set.univ).2 ?_) X hX
  intro e _
  obtain ⟨d, ⟨ed⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF.2 e
  exact (derivedFiniteCellOver A D Set.univ).prop_of_iso
    ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app _ ≪≫
      (dgDerivedRestriction A D E F).mapIso ed)
    (triaRepresentable A D d).property

/--
概要：実際の導来延長を前三角化へ制限した関手。
方針：有限 cell の保存を使って充満部分圏へ持ち上げる。
規約：周囲の導来加群圏への包含との正方形は定義上可換。
使われ方：Drinfeld §2.4、KST D4 の三角構造の比較。
-/
def triaExtension : TriaCategory A D ⥤ TriaCategory A E :=
  (derivedFiniteCellOver A E Set.univ).lift (triaInclusion A D ⋙ dgDerivedExtension A D E F)
    (fun X => extension_finiteCell A D E F X.property)

/--
概要：実際の導来制限を前三角化へ制限した関手。
方針：準同値の有限 cell 保存を用いる。
規約：逆関手を新たな選択で作り直さない。
使われ方：Drinfeld §2.4・Lemma 13.5 の逆向き比較。
-/
def triaRestriction (hF : QuasiEquivalence F) : TriaCategory A E ⥤ TriaCategory A D :=
  (derivedFiniteCellOver A D Set.univ).lift (triaInclusion A E ⋙ dgDerivedRestriction A D E F)
    (fun X => restriction_finiteCell A D E F hF X.property)

/--
概要：準同値は前三角化の圏同値を誘導する。
方針：導来随伴の単位・余単位を同じ充満部分圏へ制限する。
規約：冪等完備化は行わない。
使われ方：Drinfeld §2.4・Lemma 13.5、KST D4 の増大関手の移送。
-/
def triaEquivalence (hF : QuasiEquivalence F) : TriaCategory A D ≌ TriaCategory A E where
  functor := triaExtension A D E F
  inverse := triaRestriction A D E F hF
  unitIso := NatIso.ofComponents
    (fun X => (derivedFiniteCellOver A D Set.univ).isoMk
      ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app X.obj))
    (by intro X Y f; apply (derivedFiniteCellOver A D Set.univ).hom_ext
        exact (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun X => (derivedFiniteCellOver A E Set.univ).isoMk
      ((dgFunctorDerivedEquivalence A D E F hF).counitIso.app X.obj))
    (by intro X Y f; apply (derivedFiniteCellOver A E Set.univ).hom_ext
        exact (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom.naturality f.hom)
  functor_unitIso_comp X := by
    apply (derivedFiniteCellOver A E Set.univ).hom_ext
    exact (dgFunctorDerivedEquivalence A D E F hF).functor_unitIso_comp X.obj

end SerrePositivity.KST.DerivedGeometry.DGResolution
