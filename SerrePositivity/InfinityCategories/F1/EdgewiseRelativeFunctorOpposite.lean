module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOpposite
public import SerrePositivity.InfinityCategories.F1.EdgewiseOppositeHomEquivalence
public import SerrePositivity.InfinityCategories.F1.EdgewiseEnrichedCategory

/-!
概要：元の相対 Hom の共通解像から、反転した底上の相対 Hom への作用。
方針：左端射影と相対 Hom の反転同型を合成し、通常の内部 Hom の評価で比較する。
規約：元の写像空間の高次パラメーターも解像し、対象ごとの同値だけで代用しない。
使われ方：right fibration と反対の底上の left fibration の coherent な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 共通解像の左端と同じ相対 Hom の反転同型を続けた実際の作用。 -/
def edgewiseRelativeFunctorOpposite {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    edgewiseSubdivision (relativeFunctorSpace p a) ⟶
      relativeFunctorSpace (SSet.opFunctor.map p) (SSet.opFunctor.map a) :=
  edgewiseLeft (relativeFunctorSpace p a) ≫ (relativeFunctorOppositeIso p a).hom

/-- 相対作用を内部 Hom へ含めると、元の包含と同じ反転評価の作用になる。 -/
lemma edgewiseRelativeFunctorOpposite_ι {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    edgewiseRelativeFunctorOpposite p a ≫
      vertexFiberι ((ihom A.op).map (SSet.opFunctor.map p))
        (functorVertex (SSet.opFunctor.map a)) =
    edgewiseSubdivisionMap (vertexFiberι ((ihom A).map p) (functorVertex a)) ≫
      edgewiseOppositeKanEnrichedMap A E := by
  rw [edgewiseRelativeFunctorOpposite, Category.assoc, relativeFunctorOppositeIso_hom_ι,
    edgewiseOppositeKanEnrichedMap_eq_left]
  simp only [← Category.assoc]
  rw [edgewiseLeft_naturality]
  rfl

local instance {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    [KanComplex (relativeFunctorSpace p a)] :
    KanComplex (relativeFunctorSpace (SSet.opFunctor.map p) (SSet.opFunctor.map a)) :=
  HomotopyLimits.kanComplex_of_iso (relativeFunctorOppositeIso p a)

/-- 元の相対 Hom が Kan なら、同じ共通解像からの反転作用は同値。 -/
lemma edgewiseRelativeFunctorOpposite_isQCatEquivalence {A E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) [KanComplex (relativeFunctorSpace p a)] :
    IsQCatEquivalence (edgewiseRelativeFunctorOpposite p a) :=
  (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (relativeFunctorSpace p a))).comp
    (qCatEquivalenceOfIso (relativeFunctorOppositeIso p a)).isQCatEquivalence

end SerrePositivity.InfinityCategories
