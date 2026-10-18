import SerrePositivity.InfinityCategories.F1B
import Lean.Util.CollectAxioms

/-!
概要：α2b の全宣言を監査する。
方針：宣言元モジュールで抽出し、生成宣言を含め依存公理を再帰的に調べる。
規約：許す公理は propext・Classical.choice・Quot.sound のみ。
使われ方：B1〜B5 の保存単位で対象ビルド後に実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F1B |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "F1B: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "F1B: no declarations audited"
  logInfo m!"F1B audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.QCatAdjunction
#check @SerrePositivity.InfinityCategories.qcatCellEquiv
#check @SerrePositivity.InfinityCategories.QCatAdjunction.comp
#check @SerrePositivity.InfinityCategories.QCatAdjunction.unitHom
#check @SerrePositivity.InfinityCategories.QCatAdjunction.counitHom
#check @SerrePositivity.InfinityCategories.QCatAdjunction.left_triangle_hom
#check @SerrePositivity.InfinityCategories.QCatAdjunction.right_triangle_hom
#check @SerrePositivity.InfinityCategories.QCatAdjunction.rightAdjointFunctorIso
#check @SerrePositivity.InfinityCategories.QCatAdjunction.leftAdjointFunctorIso

#check @SerrePositivity.InfinityCategories.QCatAdjunction.homEquiv

#check @SerrePositivity.InfinityCategories.qcatHomFunctor_faithful

#check @SerrePositivity.InfinityCategories.functorCellToNatTrans_homotopy

#check @SerrePositivity.InfinityCategories.qcatCellOfHomotopy_toNatTrans

#check @SerrePositivity.InfinityCategories.QCatAdjunction.mkOfHomTriangles

#check @SerrePositivity.InfinityCategories.QCatAdjunction.homEquiv_naturality_right

#check @SerrePositivity.InfinityCategories.QCatAdjunction.homEquiv_naturality_left

#check @SerrePositivity.InfinityCategories.intervalFamilyEdgeEquiv

#check @SerrePositivity.InfinityCategories.intervalFamilyHom_surjective

#check @SerrePositivity.InfinityCategories.intervalFamilyTranspose

#check @SerrePositivity.InfinityCategories.intervalFamilyTranspose_precomp

#check @SerrePositivity.InfinityCategories.intervalFamilyHomotopyOfRightHomotopy

#check @SerrePositivity.InfinityCategories.intervalFamilyHom_eq_imp_homotopy

#check @SerrePositivity.InfinityCategories.intervalFamilyHomPrecomp

#check @SerrePositivity.InfinityCategories.intervalFamilyHom_precomp

#check @SerrePositivity.InfinityCategories.bicategoryAdjunct_whiskerLeft

#check @SerrePositivity.InfinityCategories.qcatSSetPrecomposition

#check @SerrePositivity.InfinityCategories.qcatCatPrecomposition

#check @SerrePositivity.InfinityCategories.qcatCell_whiskerLeft

#check @SerrePositivity.InfinityCategories.QCatAdjunction.homEquiv_precomp

#check @SerrePositivity.InfinityCategories.QCatAdjunction.constantHomEquiv_precomp

#check @SerrePositivity.InfinityCategories.QCatAdjunction.intervalMap_family

#check @SerrePositivity.InfinityCategories.QCatAdjunction.intervalInverse_family

#check @SerrePositivity.InfinityCategories.QCatAdjunction.intervalMap_unique_homotopy

#check @SerrePositivity.InfinityCategories.QCatAdjunction.intervalMap_isSimplicialHomotopyEquivalence

#check @SerrePositivity.InfinityCategories.PinchedInterval.comparison

#check @SerrePositivity.InfinityCategories.PinchedInterval.comparison_uncurry

#check @SerrePositivity.InfinityCategories.PinchedInterval.comparison_mono

#check @SerrePositivity.InfinityCategories.PinchedInterval.comparison_exists_retraction

#check @SerrePositivity.InfinityCategories.PinchedInterval.comparison_exists_homotopy_section

#check @SerrePositivity.InfinityCategories.PinchedInterval.comparison_isQCatEquivalence

#check @SerrePositivity.InfinityCategories.QCatAdjunction.pinchedHomEquivalence

#check @SerrePositivity.InfinityCategories.QCatAdjunction.pinchedMap_isSimplicialHomotopyEquivalence

#check @SerrePositivity.InfinityCategories.QCatAdjunction.pinchedMap_comparisonIso

#check @SerrePositivity.InfinityCategories.intervalFunctorMap_uncurry

#check @SerrePositivity.InfinityCategories.pinchedIntervalComparison_naturality

#check @SerrePositivity.InfinityCategories.qcatCell_whiskerRight

#check @SerrePositivity.InfinityCategories.constantFunctorMap

#check @SerrePositivity.InfinityCategories.constantFunctorHomMap

#check @SerrePositivity.InfinityCategories.constantFunctorHomMap_precomp

#check @SerrePositivity.InfinityCategories.constantFunctorHomMap_postcomp

#check @SerrePositivity.InfinityCategories.intervalPrecompose_family

#check @SerrePositivity.InfinityCategories.intervalPostcompose_family

#check @SerrePositivity.InfinityCategories.intervalPrecompose_comp

#check @SerrePositivity.InfinityCategories.intervalPostcompose_comp

#check @SerrePositivity.InfinityCategories.intervalPrecompose_postcompose

#check @SerrePositivity.InfinityCategories.QCatAdjunction.constantHomEquiv_naturality_left

#check @SerrePositivity.InfinityCategories.QCatAdjunction.constantHomEquiv_naturality_right

#check @SerrePositivity.InfinityCategories.QCatAdjunction.intervalMap_naturality_left

#check @SerrePositivity.InfinityCategories.QCatAdjunction.intervalMap_naturality_right

#check @SerrePositivity.InfinityCategories.PinchedInterval.liftMapCompIso

#check @SerrePositivity.InfinityCategories.QCatAdjunction.pinchedMap_naturality_left

#check @SerrePositivity.InfinityCategories.QCatAdjunction.pinchedMap_naturality_right

#check @SerrePositivity.InfinityCategories.PinchedInterval.liftMapComparisonIso

#check @SerrePositivity.InfinityCategories.PinchedInterval.precomposeCompIso

#check @SerrePositivity.InfinityCategories.PinchedInterval.postcomposeCompIso

#check @SerrePositivity.InfinityCategories.PinchedInterval.precomposePostcomposeIso
