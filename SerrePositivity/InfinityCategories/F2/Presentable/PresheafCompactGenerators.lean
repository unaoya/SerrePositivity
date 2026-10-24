module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteLeftFibrationCompact
public import SerrePositivity.InfinityCategories.F2.Presentable.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.F2.Ind.FixedVertexMapSmallness

/-!
概要：一般の小さい ∞ 圏上の前層の、小さい compact 全部分生成圏を構成する。
方針：有限底上符号族と元の全表示を分類同値で送り、小さい全部分模型へ移す。
規約：生成圏と filtered 添字は宇宙 u、前層は u+1。各指定前層を厳密な頂点にする。
使われ方：前層の accessibility と presentable 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable (C : SSet.{u}) [Quasicategory C]

omit [Quasicategory C] in
/-- 概要：元の前層 ∞ 圏では頂点を固定した小さい始域の全写像の型が小さい。
方針：空間の同じ性質を小さい底の内部 Hom へ移す。
規約：実際の全写像の小ささを述べ、局所小ささを追加仮定にしない。
使われ方：小さい compact 全部分模型の構成。 -/
lemma presheaf_hasSmallFixedVertexMaps : Ind.HasSmallFixedVertexMaps (PresheafInfinity C) := by
  have (n : SimplexCategoryᵒᵖ) :
      Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj C.op).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1, u} (C.op.obj n)))
  exact Ind.space_hasSmallFixedVertexMaps.functorSpace
    ((SSet.uliftFunctor.{u + 1, u}).obj C.op)

/-- 概要：共通の有限底上符号族を元の前層の頂点族へ分類する。
方針：反転した底上の連続置換に同じ straightening を適用する。
規約：符号型は宇宙 u の FiniteOverCode C.op。
使われ方：小さい compact 全部分生成圏の対象族。 -/
def finitePresheafGeneratorVertex (q : FiniteOverCode C.op) : (PresheafInfinity C) _⦋0⦌ :=
  (leftStraighteningInfinityMap C.op).app _ (finiteLeftFibrationGeneratorVertex q)

/-- 概要：分類した同じ小さい有限符号族の全項は compact である。
方針：元の left fibration の compact 性を同じ分類同値で輸送する。
規約：元の全 Hom による compact 性の定義を使う。
使われ方：小さい生成圏の compact 性。 -/
lemma finitePresheafGeneratorVertex_isCompact (q : FiniteOverCode C.op) :
    Compact.IsKappaCompact.{u, u + 1} Cardinal.aleph0 (finitePresheafGeneratorVertex C q) :=
  isKappaCompact_image_of_equivalence (leftStraighteningInfinityEquivalence C.op) _
    (finiteLeftFibrationGeneratorVertex_isCompact q)

/-- 概要：元の前層の共通の小さい compact 族を全部分圏として縮小する。
方針：頂点を固定した全写像の小ささで全次数を宇宙 u へ戻す。
規約：元の前層への全部分包含を保持する。
使われ方：accessibility に用いる小さい生成圏。 -/
def presheafCompactGeneratorCategory : SSet.{u} :=
  smallFullModel (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)

/-- 概要：縮小した同じ compact 生成圏は quasicategory である。
方針：小さい全部分模型の既存のホーン充填を用いる。
規約：元の前層と同じ頂点族を用いる。
使われ方：accessibility の小さい生成圏の充填性。 -/
instance presheafCompactGeneratorCategory_quasicategory :
    Quasicategory (presheafCompactGeneratorCategory C) :=
  inferInstanceAs (Quasicategory (smallFullModel
    (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)))

/-- 概要：元の前層 ∞ 圏への、同じ小さい compact 全部分模型の包含。
方針：縮小同型と元の全部分包含を合成する。
規約：対象だけでなく全写像空間の包含を保持する。
使われ方：前層の compact 生成性の公開界面。 -/
def presheafCompactGeneratorInclusion :
    (SSet.uliftFunctor.{u + 1, u}).obj (presheafCompactGeneratorCategory C) ⟶ PresheafInfinity C :=
  smallFullModelInclusion (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)

/-- 概要：同じ小さい全部分模型は元の任意の前層を compact 生成する。
方針：有限底上模型の全表示を分類し、元の前層を厳密な頂点として回収する。
規約：同型飽和内の全図式を一つの小さい全部分圏へ移す。
使われ方：一般の前層の ℵ₀-accessibility。 -/
lemma presheafCompactGeneratorInclusion_isCompactGenerating :
    IsKappaCompactGenerating Cardinal.aleph0 (presheafCompactGeneratorInclusion C) := by
  apply smallFullModelInclusion_isKappaCompactGenerating
    (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)
    (finitePresheafGeneratorVertex_isCompact C)
  intro x
  let e := leftStraighteningInfinityEquivalence C.op
  let y := e.inv.app (Opposite.op ⦋0⦌) x
  let X := coherentNerveObject y
  obtain ⟨d, hd, hv⟩ := exists_finiteLeftFibrationPresentation X
  let G := strictCoherentDiagram (finiteLeftFibrationDiagram X.val) ≫ e.hom
  let c := mapJoinCocone e.hom d
  have hc : IsColimitCone c := (equivalence_isColimitCone_iff e.isQCatEquivalence d).mp hd
  have hcv : c.vertex = e.hom.app (Opposite.op ⦋0⦌) y := by
    rw [Ind.mapJoinCocone_vertex, hv]
    exact congrArg (e.hom.app (Opposite.op ⦋0⦌)) (coherentNerveVertex_object y)
  obtain ⟨c', hc', hv'⟩ := exists_colimitCone_vertex_of_iso c hc
    (eqToIso (congrArg HomotopyCategory.mk hcv) ≪≫ e.invHomIso.app x)
  refine ⟨nerve (FiniteOverPieces X.val), inferInstance,
    finiteOverPieces_nerve_isKappaFiltered X.val, G, ?_, c', hc', hv'⟩
  intro a
  obtain ⟨q, ⟨hq⟩⟩ := finiteLeftFibrationDiagram_in_family X.val a
  exact ⟨q, ⟨VertexIso.map hq e.hom⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
