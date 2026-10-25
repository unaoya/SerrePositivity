module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.EndSectionsRelativeHom
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.PinchedHomVertexTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PinchedHomIso

/-!
概要：end 切断の模型を、Yoneda 図式から Hom 係数前層族への全自然変換空間へ移す。
方針：分類の底変換同型で終点を移し、二変数の内部 Hom を curry する。
規約：元の F・G と元の Yoneda 関手を保持する。
使われ方：P-12 の end 比較を Yoneda の左 Kan 普遍性で閉じるための模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    KanComplex (HomotopyLimits.simplicialSections (functorEndProjection F G)) :=
  HomotopyLimits.simplicialSections_kanComplex _

/-- 概要：共同 Hom を二関手の二変数へ制限した元の図式。
方針：Hom の分類図式に反変・共変の底写像を前合成する。
規約：宇宙持ち上げを一度だけ行う。使われ方：end の係数の分類模型。 -/
def functorHomBifunctorDiagram {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (A.op ⊗ A) ⟶ SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (functorHomBifunctorBase F G) ≫ twistedArrowHomInfinity C

/-- 概要：二変数の共同 Hom 図式と元の pullback の分類は全自然同型。
方針：left fibration 分類の底変換則を適用する。
規約：各値の同値だけに弱めない。使われ方：写像空間の終点の正規化。 -/
def functorHomBifunctorDiagram_classificationIso {A C : SSet.{u}} [Quasicategory C]
    (F G : A ⟶ C) :
    FunctorIso (functorHomBifunctorDiagram F G)
      (leftStraighteningInfinityDiagram (functorHomBifunctorProjection F G)) :=
  leftStraighteningInfinityDiagram_baseChangeIso (twistedArrowProjection C)
    (functorHomBifunctorBase F G)

/-- 概要：end 切断を元の Hom 二変数図式間の写像空間として表示する。
方針：分類 Hom の同値の終点を、元の共同 Hom の全自然同型で移す。
規約：Hom_A と Hom_C(F(-),G(-)) をそのまま使う。
使われ方：currying による Yoneda 図式間の写像空間への移送。 -/
def functorEndSectionsHomDiagramEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C] (F G : A ⟶ C) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (HomotopyLimits.simplicialSections (functorEndProjection F G)))
      (pinchedHom (functorVertex (twistedArrowHomInfinity A))
        (functorVertex (functorHomBifunctorDiagram F G))) :=
  (functorEndSectionsBifunctorHomEquivalence F G).trans
    (pinchedHomTargetVertexIsoEquivalence (functorVertex (twistedArrowHomInfinity A))
      (functorHomBifunctorDiagram_classificationIso F G).symm)

/-- 概要：二変数全図式の関手圏を前層値の全図式の関手圏へ curry する厳密な同型。
方針：直積の宇宙比較による前合成と内部 currying の同型を合成する。
規約：任意の A を許す。使われ方：二変数の Hom の写像空間の正規化。 -/
def homBifunctorCurryIso (A : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (A.op ⊗ A))).obj SpaceInfinity.{u} ≅
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj A)).obj (PresheafInfinity A) := by
  let e := HomotopyLimits.uliftTensorIso.{u, u + 1} A.op A
  let p : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (A.op ⊗ A))).obj SpaceInfinity.{u} ≅
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj A.op ⊗
        (SSet.uliftFunctor.{u + 1, u}).obj A)).obj SpaceInfinity.{u} := {
    hom := (pre e.inv).app SpaceInfinity.{u}
    inv := (pre e.hom).app SpaceInfinity.{u}
    hom_inv_id := by
      rw [← NatTrans.comp_app, ← pre_map, e.hom_inv_id, pre_id, NatTrans.id_app]
    inv_hom_id := by
      rw [← NatTrans.comp_app, ← pre_map, e.inv_hom_id, pre_id, NatTrans.id_app] }
  exact p ≪≫ ihomCurryIso _ _ _

/-- 概要：二変数の curry は元の図式の curry を頂点上で表す。
方針：内部前合成と内部 currying を各次数で計算する。
規約：図式を選び直さない。使われ方：元の Yoneda 頂点の同定。 -/
lemma homBifunctorCurryIso_vertex (A : SSet.{u})
    (H : (SSet.uliftFunctor.{u + 1, u}).obj (A.op ⊗ A) ⟶ SpaceInfinity.{u}) :
    (homBifunctorCurryIso A).hom.app (Opposite.op ⦋0⦌) (functorVertex H) =
      functorVertex (curry ((HomotopyLimits.uliftTensorIso A.op A).inv ≫ H)) := by
  rfl

/-- 概要：共同 Hom の両変数制限を curry すると元の Hom 係数前層族になる。
方針：uncurry の単射性と既存の係数前層族の全評価の式を使う。
規約：G の元の全図式を保持する。使われ方：end の Yoneda 模型の終点の同定。 -/
lemma functorHomBifunctorDiagram_curry {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    curry ((HomotopyLimits.uliftTensorIso A.op A).inv ≫ functorHomBifunctorDiagram F G) =
      (SSet.uliftFunctor.{u + 1, u}).map G ≫ HomotopyLimits.presheafHomWeightDiagram F := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, HomotopyLimits.presheafHomWeightDiagram_uncurry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  rfl

/-- 概要：end 切断を元の Yoneda 図式から係数前層族への全自然変換空間として表示する。
方針：Hom 二変数図式の模型を内部 currying で移し、両頂点を正規化する。
規約：元の Fun の Hom との同値性は別工程。使われ方：Yoneda の左 Kan による最終比較。 -/
def functorEndSectionsYonedaHomEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C] (F G : A ⟶ C) :
    QCatEquivalence
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (HomotopyLimits.simplicialSections (functorEndProjection F G)))
      (pinchedHom (functorVertex (yonedaInfinityMap A))
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map G ≫
          HomotopyLimits.presheafHomWeightDiagram F))) := by
  let e := (functorEndSectionsHomDiagramEquivalence F G).trans
    (qCatEquivalenceOfIso (pinchedHomIsoOfIso (homBifunctorCurryIso A)
      (functorVertex (twistedArrowHomInfinity A))
      (functorVertex (functorHomBifunctorDiagram F G))))
  simpa only [homBifunctorCurryIso_vertex, functorHomBifunctorDiagram_curry,
    yonedaInfinityMap, homInfinityJointEvaluation] using e

end SerrePositivity.InfinityCategories.F2.Presentable
