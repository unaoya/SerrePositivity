module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftFlagComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceLeftResolution

/-!
概要：一点空間からの左 Hom 比較と左解像の具体的な比較との整合性。
方針：一点空間からの内部 Hom の同型で係数を揃え、解像の標準比較の自然性を使う。
規約：二重反転の標準同型と固定済みの一点空間の Hom の同型を使う。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の比較射の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：元の空間は反転した空間への一点空間からの Hom の反転と厳密に同型。
方針：二重反転の同型から、一点空間の内部 Hom の同型の反転した逆へ続ける。
規約：順方向は左 Hom 比較へ元の空間を入力するための係数の同定。
使われ方：Kerodon §4.6.7、Corollary 5.6.0.6、左右の係数を揃える。 -/
noncomputable def pointedSpaceLeftCoefficientIso (K : KanObject.{u}) :
    K.obj ≅ (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj K)).op :=
  (SSet.opFunctorCompOpFunctorIso.app K.obj).symm ≪≫
    SSet.opFunctor.mapIso (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).symm

/-- 概要：一点空間の係数を通る左 Hom 比較は解像の座標で元の標準比較と一致する。
方針：左 Hom 比較の旗の表示を使い、内部 Hom の同型と解像の標準比較の自然性を適用する。
規約：具体的な射の等式であり、Kan 複体のホモトピー類だけの一致ではない。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の比較射の高次の自然性への接続。 -/
lemma pointedSpaceLeftHomComparison_resolution (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso K).hom ≫
      HomotopyLimits.coherentLeftHomComparison pointKanObject (kanObjectOpFunctor.obj K) ≫
      (coherentLeftPinchedFlagIso pointKanObject (kanObjectOpFunctor.obj K)).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (coherentResolutionRightAdjoint.map
          (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom)) =
    (SSet.uliftFunctor.{u + 1, u}).map (coherentLeftResolutionComparison K.obj) := by
  have h : (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).inv ≫
      coherentResolutionComparison
        (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj K)) ≫
      coherentResolutionRightAdjoint.map
        (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom =
      coherentResolutionComparison K.obj.op := by
    have hn := coherentResolutionComparisonNat.naturality
      (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom
    change (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom ≫
        coherentResolutionComparison K.obj.op =
      coherentResolutionComparison
        (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj K)) ≫
      coherentResolutionRightAdjoint.map
        (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom at hn
    rw [← hn, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
    (HomotopyLimits.coherentLeftHomComparison pointKanObject (kanObjectOpFunctor.obj K)),
    coherentLeftHomComparison_flagIso]
  change (SSet.uliftFunctor.{u + 1, u}).map
    ((SSet.opFunctorCompOpFunctorIso.app K.obj).inv ≫ SSet.opFunctor.map
      ((pointKanObjectHomIso (kanObjectOpFunctor.obj K)).inv ≫
        coherentResolutionComparison
          (SimplicialCategory.sHom pointKanObject (kanObjectOpFunctor.obj K)) ≫
        coherentResolutionRightAdjoint.map
          (pointKanObjectHomIso (kanObjectOpFunctor.obj K)).hom)) = _
  rw [h]
  rfl

/-- 概要：反転した空間値の普遍 fiber に、元の空間から標準の coherent 比較で写す。
方針：一点空間からの Hom の係数を揃え、左 Hom 比較と標準の fiber 同型へ続ける。
規約：頂点の表示だけを標準の coherent 頂点へ正規化する。
使われ方：Kerodon Corollary 5.6.0.6、解像模型に依存しない実際の fiber 比較。 -/
noncomputable def pointedSpaceLeftCoherentComparison (K : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj K.obj ⟶
      vertexFiber pointedSpaceProjection (spaceInfinityVertex (kanObjectOpFunctor.obj K)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (pointedSpaceLeftCoefficientIso K).hom ≫
    HomotopyLimits.coherentLeftHomComparison pointKanObject (kanObjectOpFunctor.obj K) ≫
    (eqToIso (congrArg₂ (fun x y ↦ pinchedHomLeft x y)
      (spaceInfinityVertex_eq_coherent pointKanObject)
      (spaceInfinityVertex_eq_coherent (kanObjectOpFunctor.obj K)))).inv ≫
    (pointedSpaceFiberPinchedIso _).inv

/-- 概要：普遍 fiber への標準の coherent 比較を解像座標へ移すと標準比較を回収する。
方針：頂点の表示を揃えて fiber と左 Hom の往復を消し、一点空間の係数の計算を使う。
規約：比較の全ての単体に対する射の等式。
使われ方：Kerodon Corollary 5.6.0.6、fiber 比較の高次の自然性と同値性の接続。 -/
lemma pointedSpaceLeftCoherentComparison_resolution (K : KanObject.{u}) :
    pointedSpaceLeftCoherentComparison K ≫ (pointedSpaceLeftResolutionIso K).hom =
    (SSet.uliftFunctor.{u + 1, u}).map (coherentLeftResolutionComparison K.obj) := by
  simp only [pointedSpaceLeftCoherentComparison, pointedSpaceLeftResolutionIso,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact pointedSpaceLeftHomComparison_resolution K

/-- 概要：左 Hom からの fiber 比較と解像模型からの具体的な比較は同じ射。
方針：解像模型の同型の順方向を両辺に後合成し、両方の計算式を適用する。
規約：同値の選択によらず、全ての次数で比較射が一致する。
使われ方：Kerodon Corollary 5.6.0.6、具体的な fiber 模型と coherent な比較の接続。 -/
lemma pointedSpaceLeftCoherentComparison_eq_resolution (K : KanObject.{u}) :
    pointedSpaceLeftCoherentComparison K = pointedSpaceLeftResolutionComparison K := by
  apply (cancel_mono (pointedSpaceLeftResolutionIso K).hom).1
  rw [pointedSpaceLeftCoherentComparison_resolution,
    pointedSpaceLeftResolutionComparison_factorization]

/-- 概要：左 Hom の標準比較から作った普遍 fiber への比較は同値。
方針：解像模型からの比較との一致を使う。
規約：始域は元の Kan 複体の宇宙持ち上げ、終域は反転した値上の fiber。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の fiber ごとの同値性。 -/
lemma pointedSpaceLeftCoherentComparison_isQCatEquivalence (K : KanObject.{u}) :
    IsQCatEquivalence (pointedSpaceLeftCoherentComparison K) := by
  rw [pointedSpaceLeftCoherentComparison_eq_resolution]
  exact pointedSpaceLeftResolutionComparison_isQCatEquivalence K

end SerrePositivity.InfinityCategories
