module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiberBaseComparison

/-!
概要：一脚が Kan fibration の二つの引き戻しの全基点 π_* 比較。
方針：射影の fiber の標準同型で元の fiber 比較へ移し、全空間比較を使う。
規約：零次数の全射性には元の全空間の頂点を明示し、空の fiber も検査する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2、Sp の引き戻しの Ω 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.FibrationSquare
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：引き戻しの第二射影は元の第一脚の Kan fibration 性を保つ。
方針：ホーンに対する RLP の引き戻し閉性を使う。
規約：選んだ標準引き戻しに限らず任意の引き戻し正方形を扱う。
使われ方：引き戻し射影の fiber の Kan 性の供給。 -/
lemma pullbackSecond_fibration {P E X B : SSet.{u}}
    {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    (hP : IsPullback i j p q) [Fibration p] : Fibration j := by
  apply (fibration_iff _).mpr
  exact J.rlp.of_isPullback hP ((fibration_iff _).mp inferInstance)

/-- 概要：三つの π_* 同型で比較した一脚 fibration の引き戻し間の射も π_* 同型。
方針：射影の fiber を元の fiber と同型で同定し、全次数と全成分の比較を移す。
規約：四角形全体の厳密可換性と元の全空間の頂点 e₀ を明示し、空の fiber を省略しない。
使われ方：HTT 4.2.4.1、BF 1978 §2、Sp の実際の引き戻しの Ω 比較。 -/
lemma pullbackComparison_piIsomorphism
    {P E X B P' E' X' B' : SSet.{u}}
    [KanComplex P] [KanComplex E] [KanComplex X] [KanComplex B]
    [KanComplex P'] [KanComplex E'] [KanComplex X'] [KanComplex B']
    {i : P ⟶ E} {j : P ⟶ X} {p : E ⟶ B} {q : X ⟶ B}
    {i' : P' ⟶ E'} {j' : P' ⟶ X'} {p' : E' ⟶ B'} {q' : X' ⟶ B'}
    (hP : IsPullback i j p q) (hP' : IsPullback i' j' p' q') [Fibration p] [Fibration p']
    (aP : P ⟶ P') (aE : E ⟶ E') (aX : X ⟶ X') (aB : B ⟶ B')
    (hi : i ≫ aE = aP ≫ i') (hj : j ≫ aX = aP ≫ j')
    (hp : p ≫ aB = aE ≫ p') (hq : q ≫ aB = aX ≫ q')
    (hE : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism aE) (hX : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism aX) (hB : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism aB)
    (e₀ : E _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism aP := by
  have : Fibration j := pullbackSecond_fibration hP
  have : Fibration j' := pullbackSecond_fibration hP'
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationTotal_piIsomorphism_of_base j j' aP aX hj hX
  · intro x v n
    let es := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso hP x (q.app _ x) rfl
    have ht : q'.app _ (aX.app _ x) = aB.app _ (q.app _ x) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq q q' aX aB hq x).symm
    let et := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso hP' (aX.app _ x) (aB.app _ (q.app _ x)) ht
    have horig := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_piIsomorphism_of_vertex p p' aE aB hp hE hB
      (q.app _ x) (es.hom.app _ v)
    have hnew := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanPiIsomorphism_of_iso_square es et _ _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso_naturality hP hP' aP aE aX aB hi hj hp x (q.app _ x) rfl ht) horig
    exact hnew v n
  · intro x
    let es := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso hP x (q.app _ x) rfl
    have ht : q'.app _ (aX.app _ x) = aB.app _ (q.app _ x) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq q q' aX aB hq x).symm
    let et := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso hP' (aX.app _ x) (aB.app _ (q.app _ x)) ht
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.piZero_surjective_of_iso_square es et _ _
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pullbackFiberIso_naturality hP hP' aP aE aX aB hi hj hp x (q.app _ x) rfl ht)
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibrationFiberMapBase_piZero_surjective p p' aE aB hp hE hB e₀ (q.app _ x)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
