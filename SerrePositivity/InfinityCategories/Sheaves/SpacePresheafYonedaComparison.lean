module

public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYonedaJointHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：固定した元の離散前層への Yoneda 射を、実際の Yoneda の同じ形状への制限と全族で比較する。
方針：共同 Hom の分類図式の指定同型を既存の底同型で制限し、全関手空間の curry で送る。
  文献対応：HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、
規約：元の公開射を保持し、表現可能値ごとの同型には置き換えない。
Corollary 5.6.0.6（Tag 028T）、S8 の重み付き右 Kan 拡張への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable (C : Type u) [SmallCategory C]

/-- 実際の Yoneda を、指定した反対 nerve の同型で元の前層の形状へ制限する。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、既存射の係数移送。 -/
def nativeSetShapeYoneda :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ PresheafCat C SpaceInfinity.{u} :=
  yonedaInfinityMap (nerve C) ≫
    (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).inv)).app
      SpaceInfinity.{u}

/-- 二変数の通常の Hom の添字移送は、実際の Hom の反対の底移送と全単体で一致する。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、同じ底の模型の合成則。 -/
lemma ordinaryHomFamilyBase_twisted :
    ordinaryHomFamilyBase C ≫ (SSet.uliftFunctor.{u + 1, u}).map (ordinaryHomBaseIso C).hom =
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveOppositeIso (C := C)).inv ▷
          (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) ≫
        (uliftTensorIso.{u, u + 1} (nerve C).op (nerve C)).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 同じ形状へ制限した実際の Yoneda は、実際の共同 Hom の同じ制限の curry。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、第一変数の制限と curry の法則。 -/
lemma nativeSetShapeYoneda_curry :
    nativeSetShapeYoneda C =
      curry (ordinaryHomFamilyBase C ≫
        (SSet.uliftFunctor.{u + 1, u}).map (ordinaryHomBaseIso C).hom ≫
          twistedArrowHomInfinity (nerve C)) := by
  rw [nativeSetShapeYoneda, yonedaInfinityMap, curry_pre_app, homInfinityJointEvaluation,
    ← Category.assoc, ← ordinaryHomFamilyBase_twisted, Category.assoc]

/-- 固定した元の離散前層への Yoneda 射と、実際の Yoneda の指定形状への制限は全族で関手同型。
HTT 5.1.5.6、Kerodon Proposition 8.1.1.10（Tag 03JN）、Corollary 5.6.0.6（Tag 028T）。
同じ全 Hom 比較を curry した指定同型であり、各対象の同型の仮定を追加しない。 -/
def fixedSetYoneda_nativeIso :
    FunctorIso (nativeSetShapeYoneda C)
      (liftedSetYoneda C ≫ (discretePresheafInclusion C).val) := by
  rw [nativeSetShapeYoneda_curry, liftedSetYoneda_jointHom_curry]
  exact ((ordinaryHomJointRealizationIso C).precomp (ordinaryHomFamilyBase C)).curry

end SerrePositivity.InfinityCategories.Sheaves
