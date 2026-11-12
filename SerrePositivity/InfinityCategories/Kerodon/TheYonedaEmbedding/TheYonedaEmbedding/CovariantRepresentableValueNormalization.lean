module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CovariantRepresentableValues

/-!
概要：共変表現可能値の元の比較から、隣接する反転比較とその逆を相殺する。
方針：同じ選ばれた同値の homInvIso を合成する。
規約：元の比較射は変更せず、その全写像間の同型を与える。
使われ方：G8 の表現可能値と標準後合成の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：元の共変表現可能値の比較は、反転した slice の値比較の逆と左右比較の合成に同型。
方針：既存の反転同値とその逆が隣り合う箇所の全族同型を使う。
規約：逆の選択を含め元の比較を保持。使われ方：同じ値比較の自然性の簡約。 -/
def covariantRepresentableValueNormalizationIso {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    FunctorIso (covariantRepresentableValueEquivalence x y).hom
      ((representablePresheafOppositeHomValueEquivalence (C := C.op)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)).inv ≫
          (pinchedHomLeftRightEquivalence x y).hom) := by
  let a := representablePresheafOppositeHomValueEquivalence (C := C.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
  let k := kanOppositeEdgewiseEquivalence
    (Basic.pinchedHom (X := C.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))
  have h := FunctorIso.postcomp (FunctorIso.precomp k.homInvIso a.inv)
    (pinchedHomLeftRightEquivalence x y).hom
  simpa only [covariantRepresentableValueEquivalence, representablePresheafValueEquivalence,
    QCatEquivalence.trans, QCatEquivalence.symm, Category.assoc, Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
