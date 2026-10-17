module
public import SerrePositivity.DifferentialGraded.Derived.RightUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleTransportComputation

/-! # 全導来前因子上の中間制限比較と右単位子 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)
  (hD : localHomKFlat A D)

local notation "QF" => Functor.obj (rightKFlatLeftRestriction A C C D F)
  (rightKFlatDiagonal A C)
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D D hD
local notation "ID" => Functor.obj (bimoduleToDerived A D D)
  (BimoduleCategory.of A D D (Bimodule.diagonal A D))
local notation "LP" P => Functor.obj
  (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P

/-- 対角のHom写像と既存の右側導来制限表示を通した、導来合成間の自然変換。 -/
def rightUnitRestrictionMiddleMap :
    L ⋙ (HD).obj ID ⟶
      (middleRestrictionDerivedSource A B C D D F hD).obj
        ((bimoduleToDerived A C D).obj (QF).obj) :=
  whiskerLeft L ((HD).map
    ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D C F) ≫
      (middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj))

/-- 実際の全導来中間比較、外側左制限比較、右単位子を続けた経路。 -/
def rightUnitRestrictionDerivedComparison : L ⋙ (HD).obj ID ⟶ L :=
  rightUnitRestrictionMiddleMap A B C D F hD ≫
    (derivedMiddleRestrictionNatTrans A B C D D F hD).app
      ((bimoduleToDerived A C D).obj (QF).obj) ≫
    (derivedBimoduleComposeKFlatIso A B C D hD QF).hom ≫
    (derivedComposeWithLeftRestrictionIso A B C C D F (rightKFlatDiagonal A C)).hom ≫
    whiskerRight (derivedRightUnitIso A B C).hom L

/-- 中間比較のsource表示同型を、前因子・後因子の既存表示に分けた計算式。 -/
lemma rightUnitRestriction_source_identification (P : BimoduleCategory A B C) :
    (middleDerivedSourceFamilyIdentification A B C D D F hD QF).hom.app P =
      ((HD).obj ((bimoduleToDerived A D D).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A C D D F).obj (QF).obj))).map
          ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      ((HD).map ((middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj)).app
        ((L).obj ((bimoduleToDerived A B C).obj P)) := rfl

/-- sourceの制限表示を前合成すると、全導来中間比較の既存モデル計算へ戻る。 -/
lemma rightUnitRestrictionMiddleMap_base_fac (P : BimoduleCategory A B C) :
    ((HD).obj ID).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (rightUnitRestrictionMiddleMap A B C D F hD).app ((bimoduleToDerived A B C).obj P) ≫
      ((derivedMiddleRestrictionNatTrans A B C D D F hD).app
        ((bimoduleToDerived A C D).obj (QF).obj)).app ((bimoduleToDerived A B C).obj P) =
    ((HD).map ((bimoduleToDerived A D D).map
        (Bimodule.diagonalRestrictionMap A D C F))).app
        ((bimoduleToDerived A B D).obj (LP P)) ≫
      derivedMiddleRestrictionCanonicalComparison A B C D D F hD P QF := by
  let a := (middleLeftRestrictionDerivedIso A B C D F).hom.app P
  let b := (HD).map ((bimoduleToDerived A D D).map
    (Bimodule.diagonalRestrictionMap A D C F))
  let c := (HD).map ((middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj)
  have hn := b.naturality a
  have hc : ((HD).obj ID).map a ≫
      (rightUnitRestrictionMiddleMap A B C D F hD).app ((bimoduleToDerived A B C).obj P) =
    b.app ((bimoduleToDerived A B D).obj (LP P)) ≫
      (middleDerivedSourceFamilyIdentification A B C D D F hD QF).hom.app P := by
    rw [rightUnitRestriction_source_identification]
    change ((HD).obj ID).map a ≫ ((HD).map
      ((bimoduleToDerived A D D).map (Bimodule.diagonalRestrictionMap A D C F) ≫
        (middleRightRestrictionDerivedIso A C D F D).hom.app (QF).obj)).app
      ((L).obj ((bimoduleToDerived A B C).obj P)) = _
    rw [(HD).map_comp, NatTrans.comp_app]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ c.app ((L).obj ((bimoduleToDerived A B C).obj P))) hn).trans
        (Category.assoc _ _ _))
  rw [← Category.assoc, hc, Category.assoc,
    derivedMiddleRestrictionNatTrans_base_fac]

end SerrePositivity.DifferentialGraded.BimoduleTensor
