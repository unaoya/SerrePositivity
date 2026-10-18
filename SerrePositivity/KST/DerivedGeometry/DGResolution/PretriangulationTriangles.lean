module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.Pretriangulation

/-!
# 前三角化の比較と shift・三角形の両立

概要：前三角化の同値に、実際の導来延長・制限の shift と三角構造を付ける。
方針：充満部分圏への包含で比較し、随伴の単位の整合性も保持する。
規約：単なる圏同値から shift との両立を推測しない。
使われ方：Drinfeld §2.4・Lemma 13.5、KST D4 の増大関手の移送。
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

local instance : (triaInclusion A D).Full :=
  inferInstanceAs ((derivedFiniteCellOver A D Set.univ).ι.Full)
local instance : (triaInclusion A D).Faithful :=
  inferInstanceAs ((derivedFiniteCellOver A D Set.univ).ι.Faithful)
local instance : (triaInclusion A E).Full :=
  inferInstanceAs ((derivedFiniteCellOver A E Set.univ).ι.Full)
local instance : (triaInclusion A E).Faithful :=
  inferInstanceAs ((derivedFiniteCellOver A E Set.univ).ι.Faithful)
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F
local instance : (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F

/--
概要：前三角化の延長と包含の可換正方形。
方針：同じ導来延長の制限であることを使う。
規約：比較同型は恒等同型。
使われ方：Drinfeld §2.4 の前三角化の両立。
-/
def extensionInclusionIso : triaExtension A D E F ⋙ triaInclusion A E ≅
    triaInclusion A D ⋙ dgDerivedExtension A D E F := Iso.refl _

/--
概要：前三角化の制限と包含の可換正方形。
方針：同じ導来制限を使う。
規約：準同値の証人を保持する。
使われ方：Drinfeld §2.4・Lemma 13.5 の逆向きの両立。
-/
def restrictionInclusionIso (hF : QuasiEquivalence F) :
    triaRestriction A D E F hF ⋙ triaInclusion A D ≅
      triaInclusion A E ⋙ dgDerivedRestriction A D E F := Iso.refl _

/--
概要：前三角化の延長は shift と両立する。
方針：包含への合成を通して既存の shift 比較を引き戻す。
規約：shift を独立に選び直さない。
使われ方：Drinfeld §2.4 の三角化の関手。
-/
instance triaExtensionCommShift : (triaExtension A D E F).CommShift ℤ :=
  Functor.CommShift.ofComp (extensionInclusionIso A D E F) ℤ

/--
概要：前三角化の制限は shift と両立する。
方針：充満忠実な包含を通して比較する。
規約：導来制限の shift を維持する。
使われ方：Drinfeld §2.4・Lemma 13.5 の逆向きの移送。
-/
instance triaRestrictionCommShift (hF : QuasiEquivalence F) :
    (triaRestriction A D E F hF).CommShift ℤ :=
  Functor.CommShift.ofComp (restrictionInclusionIso A D E F hF) ℤ

/--
概要：延長の包含正方形は shift 比較とも両立する。
方針：合成からの shift 移送の整合性を使う。
規約：同型の射の整合性を明示する。
使われ方：Drinfeld §2.4 の三角化比較の単位。
-/
instance extensionInclusionCommShift :
    NatTrans.CommShift (extensionInclusionIso A D E F).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (extensionInclusionIso A D E F) ℤ

/--
概要：制限の包含正方形は shift 比較とも両立する。
方針：合成からの shift 移送の整合性を使う。
規約：同型の射の整合性を明示する。
使われ方：Drinfeld §2.4 の三角化比較の余単位。
-/
instance restrictionInclusionCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (restrictionInclusionIso A D E F hF).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (restrictionInclusionIso A D E F hF) ℤ

/--
概要：前三角化の延長は区別三角形を保つ。
方針：包含が三角形を反映することを使い、導来延長へ帰着する。
規約：retract による完備化は行わない。
使われ方：Drinfeld §2.4 の三角化の両立。
-/
instance triaExtensionIsTriangulated : (triaExtension A D E F).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (extensionInclusionIso A D E F)).2 inferInstance

/--
概要：前三角化の制限は区別三角形を保つ。
方針：導来制限と包含の可換正方形へ帰着する。
規約：準同値による実際の逆関手を使う。
使われ方：Drinfeld §2.4・Lemma 13.5 の三角同値。
-/
instance triaRestrictionIsTriangulated (hF : QuasiEquivalence F) :
    (triaRestriction A D E F hF).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (restrictionInclusionIso A D E F hF)).2 inferInstance

/--
概要：前三角化同値の順関手に実際の延長の shift 比較を指定する。
方針：既存の制限関手の構造を使う。
規約：同値の単位を比較する前に同じ構造を固定する。
使われ方：Drinfeld §2.4・Lemma 13.5 の三角同値。
-/
instance triaEquivalenceFunctorCommShift (hF : QuasiEquivalence F) :
    (triaEquivalence A D E F hF).functor.CommShift ℤ := triaExtensionCommShift A D E F

/--
概要：前三角化同値の逆関手に実際の制限の shift 比較を指定する。
方針：導来制限からの構造を維持する。
規約：単位・余単位の比較と同じ構造を使う。
使われ方：Drinfeld §2.4・Lemma 13.5 の三角同値。
-/
instance triaEquivalenceInverseCommShift (hF : QuasiEquivalence F) :
    (triaEquivalence A D E F hF).inverse.CommShift ℤ := triaRestrictionCommShift A D E F hF

/--
概要：前三角化の同値の単位は shift と両立する。
方針：包含の忠実性で、導来随伴の単位と包含正方形の整合性へ帰着する。
規約：順逆の shift 比較を独立に選ばない。
使われ方：Drinfeld §2.4・Lemma 13.5 の三角同値の構造。
-/
theorem triaUnitCommShift (hF : QuasiEquivalence F) :
    NatTrans.CommShift (triaEquivalence A D E F hF).unitIso.hom ℤ := by
  let := dgDerivedExtensionUnit_commShift A D E F
  let I := triaInclusion A D
  let J := triaInclusion A E
  let L := dgDerivedExtension A D E F
  let R := dgDerivedRestriction A D E F
  let Lp := triaExtension A D E F
  let Rp := triaRestriction A D E F hF
  let α := extensionInclusionIso A D E F
  let β := restrictionInclusionIso A D E F hF
  have he : Functor.whiskerRight (triaEquivalence A D E F hF).unitIso.hom I =
      (Functor.leftUnitor I).hom ≫ (Functor.rightUnitor I).inv ≫
        Functor.whiskerLeft I (dgDerivedExtensionUnit A D E F) ≫
        (Functor.associator I L R).inv ≫ Functor.whiskerRight α.inv R ≫
        (Functor.associator Lp J R).hom ≫ Functor.whiskerLeft Lp β.inv ≫
        (Functor.associator Lp Rp I).inv := by
    apply NatTrans.ext
    funext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Functor.associator_inv_app, Functor.associator_hom_app]
    change (dgDerivedExtensionUnit A D E F).app X.obj =
      𝟙 _ ≫ 𝟙 _ ≫ (dgDerivedExtensionUnit A D E F).app X.obj ≫
        𝟙 _ ≫ R.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact (Category.comp_id _).symm
  exact NatTrans.CommShift.of_comp_faithful (G := I) (h := by rw [he]; infer_instance)

/--
概要：前三角化の同値は随伴全体として shift と両立する。
方針：導来随伴から制限した単位の整合性を使う。
規約：余単位の整合性も同じ随伴から得る。
使われ方：Drinfeld §2.4・Lemma 13.5 の三角構造の移送。
-/
instance triaEquivalenceCommShift (hF : QuasiEquivalence F) :
    (triaEquivalence A D E F hF).CommShift ℤ :=
  Equivalence.CommShift.mk' _ _ (triaUnitCommShift A D E F hF)

/--
概要：dg 準同値は冪等完備化前の前三角化の三角同値を与える。
方針：順向きの三角関手性と随伴の shift 整合性をまとめる。
規約：元の dg 圏の Hom の平坦性を要求しない。
使われ方：Drinfeld §2.4・Lemma 13.5、KST D4 の分解後の比較。
-/
instance triaEquivalenceIsTriangulated (hF : QuasiEquivalence F) :
    (triaEquivalence A D E F hF).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (triaEquivalence A D E F hF)
    (triaExtensionIsTriangulated A D E F)

end SerrePositivity.KST.DerivedGeometry.DGResolution
