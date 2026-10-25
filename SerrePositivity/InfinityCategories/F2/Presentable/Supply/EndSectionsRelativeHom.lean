module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.TwistedHomEndSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.PullbackSections
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningInfinityEquivalence

/-!
概要：end の切断空間を二変数の Hom 図式間の写像空間へ移す。
方針：切断を相対関手空間へ戻し、底変換と left fibration 分類の充満忠実性を使う。
規約：元の二関手と実際の Hom 射影の pullback を保持する。
使われ方：P-12 の写像空間の end 比較を Yoneda の普遍性へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance supplyEndSectionsRelativeHom_productQuasicategory
    {A : SSet.{u}} [Quasicategory A] : Quasicategory (A.op ⊗ A) :=
  quasicategory_of_innerFibration (fst A.op A)

local instance supplyEndSectionsRelativeHom_sectionsKanComplex
    {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    KanComplex (HomotopyLimits.simplicialSections (functorEndProjection F G)) :=
  HomotopyLimits.simplicialSections_kanComplex _

/-- 概要：二関手の反変・共変な両変数をまとめた底写像。
方針：F の反転と G の直積を取る。
規約：始域は元の A の二変数全体。使われ方：Hom の二変数図式の底変換。 -/
def functorHomBifunctorBase {A C : SSet.{u}} (F G : A ⟶ C) : A.op ⊗ A ⟶ C.op ⊗ C :=
  SSet.opFunctor.map F ⊗ₘ G

/-- 概要：twisted arrow への両端制限は二変数全体の底写像の制限。
方針：左右の射影の定義を比較する。
規約：射の厳密な等式。使われ方：相対関手空間の底変換。 -/
lemma functorEndPairBase_bifunctor {A C : SSet.{u}} (F G : A ⟶ C) :
    twistedArrowProjection A ≫ functorHomBifunctorBase F G = functorEndPairBase F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：二関手の共同 Hom を元の二変数上に分類する全空間。
方針：C の Hom 射影を F の反転と G の積で引き戻す。
規約：底を A の二変数全体とする。使われ方：Hom_A からの相対写像空間。 -/
def functorHomBifunctorTotal {A C : SSet.{u}} (F G : A ⟶ C) : SSet.{u} :=
  pullback (twistedArrowProjection C) (functorHomBifunctorBase F G)

/-- 概要：二変数上の Hom の分類全空間の射影。
方針：実 pullback の第二射影を使う。
規約：元の二変数を保持する。使われ方：left fibration 分類の入力。 -/
def functorHomBifunctorProjection {A C : SSet.{u}} (F G : A ⟶ C) :
    functorHomBifunctorTotal F G ⟶ A.op ⊗ A :=
  pullback.snd (twistedArrowProjection C) (functorHomBifunctorBase F G)

/-- 概要：共同 Hom の二変数への底変換も left fibration。
方針：元の twisted arrow 射影の pullback 安定性を使う。
規約：A の quasicategory 性はこの段階では不要。
使われ方：二変数図式の相対 Hom の Kan 性。 -/
instance functorHomBifunctorProjection_leftFibration {A C : SSet.{u}} [Quasicategory C]
    (F G : A ⟶ C) : LeftFibration (functorHomBifunctorProjection F G) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := twistedArrowProjection C))⟩

/-- 概要：end 切断は Hom_A から二関手の Hom への相対関手空間と厳密に同型。
方針：切断の相対関手表示と二段の pullback の底変換同型を合成する。
規約：単なる各頂点の対応に弱めない。使われ方：分類同値による二変数 Hom への移送。 -/
def functorEndSectionsRelativeHomIso {A C : SSet.{u}} (F G : A ⟶ C) :
    HomotopyLimits.simplicialSections (functorEndProjection F G) ≅
      relativeFunctorSpace (functorHomBifunctorProjection F G) (twistedArrowProjection A) :=
  HomotopyLimits.pullbackSectionsRelativeIso (twistedArrowProjection C) (functorEndPairBase F G) ≪≫
    eqToIso (congrArg (relativeFunctorSpace (twistedArrowProjection C))
      (functorEndPairBase_bifunctor F G).symm) ≪≫
    (relativeFunctorBaseChangeIso (twistedArrowProjection C)
      (functorHomBifunctorBase F G) (twistedArrowProjection A)).symm

/-- 概要：left fibrations の相対 Hom は元の分類図式間の全自然変換空間と同値。
方針：豊穣 Hom の coherent 比較に、元の分類写像の充満忠実性を合成する。
規約：既存の分類写像そのものを使う。使われ方：end の二変数の分類図式間への移送。 -/
def relativeHomStraighteningEquivalence {E E' B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q p))
      (pinchedHom (functorVertex (leftStraighteningInfinityDiagram p))
        (functorVertex (leftStraighteningInfinityDiagram q))) := by
  let e := (leftFibrationInfinityMappingEquivalence p q).trans
    (((leftStraighteningInfinityMap_isFullyFaithful B)
      (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)).isQCatEquivalence.choose)
  simpa only [leftStraighteningInfinityDiagram_vertex] using e

/-- 概要：end 切断の持ち上げは二変数 Hom の分類図式間の写像空間と同値。
方針：相対関手空間の厳密な同型を宇宙変更し、分類の Hom 同値を適用する。
規約：元の Hom_A と共同 Hom の底変換を始点・終点に固定する。
使われ方：P-12 の end 比較を Yoneda の変換空間へ読む入口。 -/
def functorEndSectionsBifunctorHomEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C] (F G : A ⟶ C) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (HomotopyLimits.simplicialSections (functorEndProjection F G)))
      (pinchedHom (functorVertex (twistedArrowHomInfinity A))
        (functorVertex (leftStraighteningInfinityDiagram (functorHomBifunctorProjection F G)))) :=
  (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
    (functorEndSectionsRelativeHomIso F G))).trans
      (relativeHomStraighteningEquivalence (twistedArrowProjection A)
        (functorHomBifunctorProjection F G))

end SerrePositivity.InfinityCategories.F2.Presentable
