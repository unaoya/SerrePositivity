module
public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting

/-! # anodyne 局所化の比較から L9 の全基点 π_* への接続
概要：局所化で可逆な Kan 複体間の射は L9 の全基点 π_* 同型。
方針：ホーン分解の右因子を全単射に対する RLP へ強め、L9 の二つの π_* 定理を合成する。
規約：HT-KQ や π_* 同型の追加公理を仮定しない。使われ方：零段を潰す実現模型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel

/-- 概要：局所化可逆な Kan 複体間の射は全基点 π_* 同型。
方針：anodyne・Kan fibration 分解の右因子を HA の局所化検出で単射 RLP にし、L9 の π_* 比較を使う。
規約：全自然数次数と全基点を含む。使われ方：Kan 模型の実際の π_* の比較。 -/
lemma kanPiIsomorphism_of_localized_isIso {A B : SSet.{u}} [KanComplex A] [KanComplex B]
    (f : A ⟶ B) (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  let F := AnodyneKanReplacement.factorization
  let i : A ⟶ F.Z.obj (Arrow.mk f) := F.i.app (Arrow.mk f)
  let p : F.Z.obj (Arrow.mk f) ⟶ B := F.p.app (Arrow.mk f)
  have hi : anodyneExtensions i := F.hi _
  have hp : J.rlp p := F.hp _
  have fac : i ≫ p = f := F.fac_app
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).2 hp
  have : KanComplex (F.Z.obj (Arrow.mk f)) := by
    change Fibration (terminal.from (F.Z.obj (Arrow.mk f)))
    rw [show terminal.from (F.Z.obj (Arrow.mk f)) = p ≫ terminal.from B from terminal.hom_ext _ _]
    infer_instance
  let Q := AnodyneHomotopy.anodyneQ
  have hQi : IsIso (Q.map i) := (Localization.inverts Q anodyneExtensions) i hi
  have hQp : IsIso (Q.map p) := by
    have hfac : Q.map i ≫ Q.map p = Q.map f := (Q.map_comp i p).symm.trans (congrArg Q.map fac)
    have : IsIso (Q.map i ≫ Q.map p) := hfac.symm ▸ hf
    exact (isIso_comp_left_iff (Q.map i) (Q.map p)).1 this
  have hr := KanFibrationLocalizedLifting.of_localized_isIso p hp
    ((SSet.modelCategoryQuillen.fibration_iff _).1 (inferInstance : Fibration (terminal.from B))) hQp
  have hπi := Spectra.kanPiIsomorphism_of_anodyne i hi
  have hπp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight p hr
  exact fac ▸ hπi.comp hπp

/-- 概要：局所化可逆な点つき射の Kan 置換は全基点 π_* 同型。
方針：Kan テストで置換後の局所化可逆性を得て、Kan 複体間の比較へ渡す。
規約：元の二つの対象の Kan 性は不要。使われ方：自然な基点を持つ実現の比較。 -/
lemma pointedKanReplacement_map_piIsomorphism_of_localized_isIso
    {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (Spectra.PointedKanReplacement.map f).right := by
  apply kanPiIsomorphism_of_localized_isIso
  exact (KanTestDetection.anodyneQ_isIso_iff_tests _).2
    (KanTestDetection.replacement_tests f.right (KanTestDetection.tests_of_anodyneQ_isIso f.right hf))

end SerrePositivity.KST.SConstruction
