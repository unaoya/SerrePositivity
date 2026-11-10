module
public import SerrePositivity.KST.ProExcision.TensorHomotopyNaturality
public import SerrePositivity.KST.ProExcision.MooreHomotopyNaturality

/-!
# Moore 収縮の全テンソルの自然性

概要：実 Moore 収縮を全テンソルへ移したホモトピーの成分が二つの入力に自然。
方針：Moore 射影の自然性と構成済み収縮の成分の自然性を一般のテンソル移送補題へ適用する。
規約：KST Construction A.5、外部群の作用にもそのまま適用する。
使われ方：正規化 EZ ホモトピー全体の同変性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
variable {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)}

/-- 概要：Moore 比較の実ホモトピー同値の収縮成分は入力の射に自然。
方針：定義に含まれる等式ホモトピーの零成分を除いて PInfty 収縮の自然性を使う。
規約：KST A.5。使われ方：テンソルへ移す第一・第二因子の自然性。 -/
lemma mooreRetractionHomotopy_naturality (f : C ⟶ C') (n : ℕ) :
    ((alternatingFaceMapComplex _).map f).f n ≫
        (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := C')).homotopyInvHomId.hom
          n (n + 1) =
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := C)).homotopyInvHomId.hom
        n (n + 1) ≫ ((alternatingFaceMapComplex _).map f).f (n + 1) := by
  simp only [homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex,
    Homotopy.trans_hom, Homotopy.ofEq_hom, Pi.zero_apply, zero_add]
  exact moorePInftyHomotopy_naturality f n

/-- 概要：Moore 射影・包含の合成は鎖写像として自然。
方針：合成を PInfty と同定してその自然性を使う。
規約：KST A.5。使われ方：テンソル収縮の零端の自然性。 -/
lemma mooreProjectionRetraction_naturality (f : C ⟶ C') :
    (alternatingFaceMapComplex _).map f ≫
        (PInftyToNormalizedMooreComplex C' ≫ inclusionOfMooreComplexMap C') =
      (PInftyToNormalizedMooreComplex C ≫ inclusionOfMooreComplexMap C) ≫
        (alternatingFaceMapComplex _).map f := by
  rw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
    PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
  exact (natTransPInfty _).naturality f

/-- 概要：Moore 収縮の全テンソルは二つの入力の射に成分ごとに自然。
方針：構成済みの二つの収縮の自然性をテンソルホモトピーの自然性へ適用する。
規約：KST Construction A.5、比較の同変性を仮定に追加しない。
使われ方：正規化した標準 EZ 比較の外部群同変性。 -/
lemma chainIntegerTensorMooreRetraction_naturality (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
        ((alternatingFaceMapComplex _).map g)).f n ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMooreRetraction C' D').hom n (n + 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMooreRetraction C D).hom n (n + 1) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap ((alternatingFaceMapComplex _).map f)
          ((alternatingFaceMapComplex _).map g)).f (n + 1) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMooreRetraction, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, add_zero]
  exact chainIntegerTensorHomotopyToId_naturality _ _ _ _
    ((alternatingFaceMapComplex _).map f) ((alternatingFaceMapComplex _).map g)
    (mooreProjectionRetraction_naturality g) (mooreRetractionHomotopy_naturality f)
    (mooreRetractionHomotopy_naturality g) n

end SerrePositivity.KST.ProExcision
