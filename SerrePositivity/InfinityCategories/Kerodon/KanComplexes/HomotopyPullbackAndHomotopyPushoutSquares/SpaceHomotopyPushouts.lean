module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.AnodyneKanCocones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.OppositeSpanIndex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCoconeLegs

/-!
概要：左脚が単射な Kan 複体の span の homotopy 押し出しを 𝒮 の実際の余極限余錐として構成する。
方針：台の押し出しを anodyne に Kan 置換し、反変 Hom の一脚 fibration の cospan で判定する。
規約：通常の押し出しが Kan であることは仮定しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.3.12（Tag 03B1）・7.5.4.6（Tag 03BB）、F2 の 𝒮 の homotopy 押し出し。

対応節は Kerodon 3.4（Tag 0106）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares
noncomputable section

/-- 概要：Kan 複体の span の台の押し出しを Kan 置換した対象。
方針：通常の単体集合の colimit にホーンの小対象論法による置換を適用する。
規約：対象の構成には脚の単射性を要求しない。
使われ方：HTT 4.2.4.1、𝒮 の実際の homotopy 押し出し対象。 -/
def kanHomotopyPushoutObject (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObject (colimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))

/-- 概要：元の span から Kan 置換した押し出しへの通常の余錐。
方針：台の押し出しの各包含を anodyne な置換の単位で後合成する。
規約：元の図式 F を保持する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、native な homotopy 押し出し余錐への入力。 -/
def kanHomotopyPushoutCocone (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) : Cocone F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.anodyneKanCocone (colimit.cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))

/-- 概要：置換前の押し出しの全反変 Hom の錐は標準 cospan 上で極限。
方針：台の余極限の反変内部 Hom の普遍性を標準の添字へ移す。
規約：台の押し出しの Kan 性を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、押し出しの Hom の厳密な普遍性。 -/
def underlyingPushoutHomCospan_isLimit
    (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    IsLimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.underlyingKanCoconeHomCone (colimit.cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) X).whisker
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex) :=
  by
    let h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.underlyingKanCoconeHomCone_isLimit _ (colimit.isColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) X
    exact h.whiskerEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndexEquivalence

/-- 概要：左脚が台で単射な span の押し出しの反転 Hom 錐の標準 end 比較は同値。
方針：単射による前合成の Kan fibration 性と厳密な Hom の極限性を cospan の比較へ渡す。
規約：右脚の単射性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.3.12（Tag 03B1）・7.5.4.6（Tag 03BB）、Kan 置換後の余錐の判定。 -/
lemma underlyingPushoutHomCospanComparison_homotopyEquivalence
    (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    [Mono ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))]
    (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison
      (SSet.opFunctor.mapCone
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.underlyingKanCoconeHomCone (colimit.cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) X).whisker
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex))) := by
  have : ∀ i, KanComplex
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X) ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex.obj i).unop) X.unop).op)
  have hf : Fibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X).map
      (AsSmall.up.map WalkingCospan.Hom.inl)) := by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ).obj
      (Opposite.op X)).map _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectOppositeHomFunctor_eq X.unop]
    change Fibration ((pre ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
      (AsSmall.up.map WalkingSpan.Hom.fst))).app X.unop.obj)
    infer_instance
  have : Fibration (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F.op X) ⋙ SSet.opFunctor).map
      (AsSmall.up.map WalkingCospan.Hom.inl)) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence _ _
    (isLimitOfPreserves SSet.opFunctor (underlyingPushoutHomCospan_isLimit F X))

/-- 概要：F1 の元の空間値 span 上の実際の homotopy 押し出し余錐。
方針：通常の Kan な余錐を coherent nerve に写し、元の図式に等式で移す。
規約：図式の対象と射は変更しない。
使われ方：HTT 4.2.4.1、F2 の 𝒮 の homotopy 押し出し。 -/
def spaceHomotopyPushoutCocone (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (kanHomotopyPushoutCocone F))

/-- 概要：homotopy 押し出し余錐の頂点は台の押し出しの Kan 置換の標準頂点。
方針：通常の余錐と図式の移送の頂点の式を使う。
規約：使った Kan 置換対象そのものを指定する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、実際の homotopy 押し出しの対象の同定。 -/
lemma spaceHomotopyPushoutCocone_vertex (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (spaceHomotopyPushoutCocone F).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (kanHomotopyPushoutObject F) := by
  rw [spaceHomotopyPushoutCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  rfl

/-- 概要：homotopy 押し出し余錐の指定した頂点からの脚。
方針：元の span の標準頂点で native な余錐を制限する。
規約：i は WalkingSpan の三つの対象のいずれでもよい。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、押し出しの実際の包含射の同定。 -/
def spaceHomotopyPushoutCoconeLeg (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (i : WalkingSpan) : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap (spaceHomotopyPushoutCocone F)
    (SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (AsSmall.up.obj i))))

/-- 概要：homotopy 押し出し余錐の脚は元の包含と Kan 置換の単位の合成の coherent 表示。
方針：元の図式への移送が脚を保持することと通常の余錐の各脚の等式を使う。
規約：包含射と置換射の実際の合成を指定する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、押し出しの実際の脚の照合。 -/
lemma spaceHomotopyPushoutCoconeLeg_eq (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (i : WalkingSpan) :
    spaceHomotopyPushoutCoconeLeg F i = SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ (show F.obj (AsSmall.up.obj i) ⟶ kanHomotopyPushoutObject F from
          (show (F.obj (AsSmall.up.obj i)).obj ⟶ (kanHomotopyPushoutObject F).obj from
            colimit.ι (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (AsSmall.up.obj i) ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.anodyneKanObjectUnit (colimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)))))) := by
  unfold spaceHomotopyPushoutCoconeLeg spaceHomotopyPushoutCocone
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentCoconeLegMap_ofDiagramEq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCoconeLeg_eq (kanHomotopyPushoutCocone F) (AsSmall.up.obj i)

/-- 概要：左脚が台で単射な Kan 複体の span の Kan 置換した押し出しは 𝒮 の余極限。
方針：単位による Hom の同値を消去し、置換前の一脚 fibration の cospan 比較へ帰着する。
規約：台の押し出しの Kan 性や追加の比較同値は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.3.12（Tag 03B1）・7.5.4.6（Tag 03BB）、F2 の homotopy 押し出し。 -/
lemma spaceHomotopyPushoutCocone_isColimitCone (F : AsSmall.{u} WalkingSpan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    [Mono ((F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (spaceHomotopyPushoutCocone F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (kanHomotopyPushoutCocone F))).mp
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.anodyneKanCocone_isColimit_iff_reflectedHomComparison
    (colimit.cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.oppositeSpanIndex).mpr
  exact underlyingPushoutHomCospanComparison_homotopyEquivalence F

end
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares
