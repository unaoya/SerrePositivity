module

public import SerrePositivity.KST.Spectra.FilteredPiIsomorphism
public import SerrePositivity.KST.Spectra.FilteredLoopColimit
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.KST.Spectra.FiberOmegaSpectrum

/-!
概要：Ω スペクトルの filtered diagram の段ごとの余極限とその BF 置換。
方針：suspension の余極限保存で構造射を作り、loop の保存と全基点の π_* 比較で Ω 条件を移す。
規約：Sp の ∞ 余極限としての普遍性はここでは主張しない。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。L9d の telescope の構成材料。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Ω スペクトルの指定段を点つき単体集合として評価する関手。
方針：対象は段、射はその段の成分とする。
規約：通常の厳密な射の圏の関手。
使われ方：BF 1978 §2、HA §1.4.2。段ごとの filtered colimit の図式。 -/
def levelEvaluation (k : ℕ) : OmegaSpectrum.{u} ⥤ PointedSimplicialSet.{u} where
  obj X := (X.level k).space
  map f := f.app k
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 概要：Ω スペクトルの図式を一段で評価した図式。
方針：段評価関手を後合成する。
規約：基点は元の段の基点。
使われ方：BF 1978 §2、HA §1.4.2。filtered Kan 列の各段。 -/
abbrev levelDiagram {J : Type u} [SmallCategory J] (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :=
  D ⋙ levelEvaluation k

/-- 概要：段評価の図式の各対象は Kan。
方針：Ω スペクトルの各段の Kan 性を使う。
規約：diagram の filtered 性は不要。
使われ方：BF 1978 §2。段ごとの Kan 余極限。 -/
instance levelDiagram_kanComplex {J : Type u} [SmallCategory J]
    (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    ∀ j, KanComplex ((levelDiagram D k).obj j).right :=
  fun j ↦ inferInstanceAs (KanComplex ((D.obj j).level k).space.right)

/-- 概要：構造射は段の図式の suspension から次段への自然変換。
方針：スペクトルの厳密な射の構造条件を自然性として使う。
規約：suspension は円の左 smash。
使われ方：BF 1978 §2、HA §1.4.2。余極限上の構造射の定義。 -/
def structureTransformation {J : Type u} [SmallCategory J]
    (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    levelDiagram D k ⋙ tensorLeft PointedSimplicialSet.circle.{u} ⟶ levelDiagram D (k + 1) where
  app j := (D.obj j).sigma k
  naturality _ _ f := (D.map f).comm k

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 概要：元の構造射を次段の余極限への cocone として表す。
方針：次段の余極限 cocone に構造射の自然変換を前合成する。
規約：定義域は現在の段の suspension の図式。
使われ方：BF 1978 §2、HA §1.4.2。余極限の構造射の普遍的定義。 -/
def structureColimitCocone (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    Cocone (levelDiagram D k ⋙ tensorLeft PointedSimplicialSet.circle.{u}) :=
  (Cocone.precompose (structureTransformation D k)).obj (colimit.cocone (levelDiagram D (k + 1)))

/-- 概要：Ω スペクトルの filtered diagram の段ごとの Kan 余極限の列。
方針：各段で余極限を取り、suspension の余極限保存の普遍性で構造射を作る。
規約：構造射の単射性は後で cofibrant 置換する。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。telescope の Kan 列の模型。 -/
def filteredKanSequence (D : J ⥤ OmegaSpectrum.{u}) : KanSequence.{u} where
  level k := {
    space := colimit (levelDiagram D k)
    kan := pointedFilteredColimit_kanComplex (levelDiagram D k) }
  sigma k := (isColimitOfPreserves (tensorLeft PointedSimplicialSet.circle.{u})
    (colimit.isColimit (levelDiagram D k))).desc (structureColimitCocone D k)

/-- 概要：各 Ω スペクトルから段ごとの Kan 余極限列への厳密な射。
方針：各段の余極限への標準射を使い、構造条件を余極限の計算式から得る。
規約：出力は単射置換前の Kan 列への射。
使われ方：BF 1978 §2、HA §1.4.2。余極限の随伴構造射の比較。 -/
def filteredKanInjection (D : J ⥤ OmegaSpectrum.{u}) (j : J) :
    KanSequence.Hom (D.obj j).toKanSequence (filteredKanSequence D) where
  app k := colimit.ι (levelDiagram D k) j
  comm k := (isColimitOfPreserves (tensorLeft PointedSimplicialSet.circle.{u})
    (colimit.isColimit (levelDiagram D k))).fac (structureColimitCocone D k) j

/-- 概要：随伴構造射は段の図式から次段の loop 図式への自然変換。
方針：厳密な構造射の可換式を suspension と loop の随伴で移す。
規約：各成分は元の Ω 条件の射。
使われ方：BF 1978 §2、HA §1.4.2。filtered colimit での Ω 条件の証明。 -/
def adjointTransformation (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    levelDiagram D k ⟶ levelDiagram D (k + 1) ⋙ ihom PointedSimplicialSet.circle.{u} where
  app j := (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((D.obj j).level k).space
    ((D.obj j).level (k + 1)).space) ((D.obj j).sigma k)
  naturality _ _ f := (sequenceHom (D.map f)).adjoint_comm k

/-- 概要：余極限列の随伴構造射は段の随伴構造射の余極限と loop 比較の合成。
方針：各段への制限を計算し、厳密な注入射の随伴構造条件と比較する。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2、HA §1.4.2。全基点 π_* 同型を余極限の Ω 条件へ移す。 -/
theorem filteredAdjoint_formula (D : J ⥤ OmegaSpectrum.{u}) (k : ℕ) :
    colimMap (adjointTransformation D k) ≫ (loopFilteredColimitIso (levelDiagram D (k + 1))).hom =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((filteredKanSequence D).level k).space
        ((filteredKanSequence D).level (k + 1)).space) ((filteredKanSequence D).sigma k) := by
  let a : colimit (levelDiagram D k) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (colimit (levelDiagram D (k + 1))) :=
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((filteredKanSequence D).level k).space
      ((filteredKanSequence D).level (k + 1)).space) ((filteredKanSequence D).sigma k)
  change colimMap (adjointTransformation D k) ≫
    (loopFilteredColimitIso (levelDiagram D (k + 1))).hom = a
  apply colimit.hom_ext
  intro j
  have hι : colimit.ι (levelDiagram D k) j ≫ colimMap (adjointTransformation D k) =
      (adjointTransformation D k).app j ≫
        colimit.ι (levelDiagram D (k + 1) ⋙ ihom PointedSimplicialSet.circle.{u}) j :=
    colimit.ι_map (adjointTransformation D k) j
  rw [← Category.assoc, hι, Category.assoc, loopFilteredColimitIso_ι]
  exact ((filteredKanInjection D j).adjoint_comm k).symm

/-- 概要：段ごとの filtered Kan 余極限列は全基点の Ω 条件を持つ。
方針：随伴構造射の段ごとの π_* 同型を filtered colimit へ移し、loop 比較同型を合成する。
規約：零次数を含み、構造射の単射性とは独立に証明する。
使われ方：BF 1978 §2、Goerss–Jardine I §7、HA §1.4.2。telescope の Ω 条件。 -/
theorem filteredKanSequence_omegaCondition (D : J ⥤ OmegaSpectrum.{u}) :
    (filteredKanSequence D).OmegaCondition := by
  intro k
  let E := levelDiagram D (k + 1) ⋙ ihom PointedSimplicialSet.circle.{u}
  let : ∀ j, KanComplex (E.obj j).right := fun j ↦
    loopSpace_kanComplex ((D.obj j).level (k + 1)).space
  have hcolim : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (colimMap (adjointTransformation D k)).right :=
    pointedColimMap_kanPiIsomorphism _ (fun j ↦ (D.obj j).omega_condition k)
  let e : (colimit E).right ≅ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (colimit (levelDiagram D (k + 1)))).right :=
    PointedSimplicialSet.forget.mapIso (loopFilteredColimitIso (levelDiagram D (k + 1)))
  have he : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso e
  have h := hcolim.comp he
  have hformula := congrArg Under.Hom.right (filteredAdjoint_formula D k)
  change (colimMap (adjointTransformation D k)).right ≫ e.hom = _ at hformula
  rw [hformula] at h
  exact h

/-- 概要：段ごとの filtered Ω 余極限列を BF cofibrant–fibrant 対象へ束ねる。
方針：検証済みの Ω 条件を持つ Kan 列の単射置換を使う。
規約：Sp の ∞ 余極限の普遍性は主張しない。
使われ方：BF 1978 §2、HA §1.4.2。L9d の telescope の対象の構成材料。 -/
def filteredOmegaSpectrum (D : J ⥤ OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  (filteredKanSequence D).cofibrantOmegaSpectrum (filteredKanSequence_omegaCondition D)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
