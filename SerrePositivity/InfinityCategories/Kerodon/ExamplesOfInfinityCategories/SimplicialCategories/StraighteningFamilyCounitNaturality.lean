module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.StraighteningFamilyRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPrecompositionCoherence

/-!
概要：任意の族と普遍族の余単位の比較を通常のパラメーター前合成で記述する。
方針：curry の往復の等式を明示した余単位に族の底変換の可換式を適用する。
規約：個々の頂点ではなく族全体の同型の等式を与える。
使われ方：普遍余単位と選択分類の成分を同じ比較にそろえる。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：関手空間への族の分類を元の族そのものへ比較する余単位。
方針：積の底上の余単位を curry し元の族への往復の等式を合成する。
規約：終点は curry・uncurry の表示でなく入力した族そのもの。
使われ方：パラメーター制限と普遍族の比較の共通の終点。 -/
def coherentStraighteningCurriedCounit {B K : SSet.{u + 1}}
    (t : K ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallFiberLeftStraighteningDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (uncurry t))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.leftUnstraighteningProjection_hasSmallSimplexFibers _))) t :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyCounit (uncurry t) ≪≫
    eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)) (curry_uncurry t))

/-- 概要：族の余単位は任意のパラメーター制限と分類の制限比較に関して可換。
方針：積の底上の余単位の自然性に curry の往復の等式を合成する。
規約：入力の族そのものを終点として全高次単体を比較する。
使われ方：個々に分類した族の余単位を制限する。 -/
lemma coherentStraighteningCurriedCounit_naturality {B K L : SSet.{u + 1}}
    (t : K ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (i : L ⟶ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyRestrictionIso t i ≪≫
      (coherentStraighteningCurriedCounit t).precomp i =
      coherentStraighteningCurriedCounit (i ≫ t) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyCounit_baseChange_naturality
    (uncurry (i ≫ t)) (uncurry t) i (uncurry_natural_left i t).symm
  have hh := congrArg (fun e ↦ e ≪≫
    eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
      (curry_uncurry (i ≫ t)))) hn
  have hq := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_eqToIso (curry_uncurry t) i
  apply Iso.ext
  have hhom := congrArg Iso.hom hh
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyRestrictionIso, coherentStraighteningCurriedCounit,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_trans, hq, Iso.trans_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc] using hhom

/-- 概要：普遍余単位は全図式を入力する族の余単位そのもの。
方針：恒等関手が表す普遍図式の定義を展開する。
規約：両者で同じ表現の選択を使う。
使われ方：普遍族への特殊化で余単位の選択を変えない。 -/
lemma universalCoherentReconstructionCounitIso_eq (B : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.universalCoherentReconstructionCounitIso B =
      coherentStraighteningCurriedCounit (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})) := rfl

/-- 概要：普遍余単位を任意の族へ制限する経路はその族の選択余単位と一致する。
方針：普遍図式への底変換の自然性を元の族への終点の等式と合成する。
規約：普遍分類と族の選択分類を同じ比較で接続する。
使われ方：全図式の余単位と個別の選択の整合性。 -/
lemma coherentStraighteningCurriedCounit_universal {B K : SSet.{u + 1}}
    (t : K ⟶ (ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyUniversalIso t ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.universalCoherentReconstructionCounitIso B).precomp t =
      coherentStraighteningCurriedCounit t := by
  let U := uncurry (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))
  have h : (B ◁ t) ≫ U = uncurry t := by
    rw [← uncurry_natural_left, Category.comp_id]
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyCounit_baseChange_naturality (uncurry t) U t h
  have hh := congrArg (fun e ↦ e ≪≫
    eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d))
      (curry_uncurry t))) hn
  have hq := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_eqToIso (curry_uncurry (𝟙 ((ihom B).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))) t
  apply Iso.ext
  have hhom := congrArg Iso.hom hh
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentStraighteningFamilyUniversalIso, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.universalCoherentReconstructionCounitIso,
    coherentStraighteningCurriedCounit, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIso.precomp_trans, hq,
    Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc, U] using hhom

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
