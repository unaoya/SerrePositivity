module

public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYonedaComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanLimitIsoTransport

/-!
概要：固定した元の反対 Yoneda 射を、実際の Yoneda から移した同じ形状の射と比較する。
方針：検証済みの全族の指定同型を反転し、同じ前層形状への前合成を行う。
規約：元の oppositeSpaceYoneda を変えず、局所極限と指定右 Kan 延長の存在を比較する。
使われ方：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の固定射への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable (C : Type u) [SmallCategory C]

/-- 実際の Yoneda を、元の反対 Yoneda と同じ指定形状の射へ移す。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、既存の反転と前合成の特殊化。 -/
def nativeSetShapeOppositeYoneda :
    presheafShape C ⟶ (PresheafCat C SpaceInfinity.{u}).op :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).inv ≫
    (uliftOppositeIso (nerve C)).hom ≫ SSet.opFunctor.map (nativeSetShapeYoneda C)

/-- 元の反対 Yoneda 射と実際の Yoneda からの指定形状の射は全族で関手同型。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、同じ全族の反転と制限の法則。 -/
def fixedOppositeSetYoneda_nativeIso :
    FunctorIso (oppositeSpaceYoneda C) (nativeSetShapeOppositeYoneda C) :=
  FunctorIso.precomp
    (f := SSet.opFunctor.map (liftedSetYoneda C ≫ (discretePresheafInclusion C).val))
    (g := SSet.opFunctor.map (nativeSetShapeYoneda C))
    (fixedSetYoneda_nativeIso C).op.symm
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).inv ≫
      (uliftOppositeIso (nerve C)).hom)

/-- 元の反対 Yoneda の局所図式と、実際の Yoneda を移した局所図式は極限の存在が同値。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、指定同型による底移送の法則。 -/
lemma hasLimit_fixedYonedaDiagram_iff_nativeShape {E : SSet.{u + 1}} [Quasicategory E]
    (O : Presheaf C E) (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    HasLimit (rightKanDiagram (oppositeSpaceYoneda C) O P) ↔
      HasLimit (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P) :=
  hasLimit_rightKanDiagram_iff_of_functorIso (fixedOppositeSetYoneda_nativeIso C) O P

/-- 元の反対 Yoneda の指定右 Kan 延長の存在は、実際の Yoneda の指定形状版の存在と同値。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、元の指定変換を構成するための移送則。 -/
lemma exists_weightedSections_iff_nativeShape {E : SSet.{u + 1}} [Quasicategory E]
    (O : Presheaf C E) :
    (∃ (G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E)
      (ε : SSet.Homotopy (oppositeSpaceYoneda C ≫ G) O),
      IsRightKanExtension (oppositeSpaceYoneda C) O G ε) ↔
    (∃ (G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E)
      (ε : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O),
      IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G ε) :=
  exists_rightKanExtension_iff_of_functorIso (fixedOppositeSetYoneda_nativeIso C) O

end SerrePositivity.InfinityCategories.Sheaves
