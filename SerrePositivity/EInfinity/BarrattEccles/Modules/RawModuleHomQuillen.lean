module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction

/-!
# 元の半自由加群からの全 Hom 関手の Quillen 条件

概要：M10 の具体的な frame 比較へ、N01 と同じ全 Hom の保存則を渡す。
方針：実半自由 filtration の全次数の持ち上げと、既存の擬同型保存を束ねる。
規約：Keller, On differential graded categories, Theorem 3.2 (1)。
使われ方：正規化単体の source frame を同じ加群へ送る随伴の右側。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A]

/-- 概要：元の半自由加群からの全 Hom は次数別全射を次数別全射へ送る。
方針：同じ filtration の全次数の持ち上げを使う。
規約：Keller Theorem 3.2 (1)、元の全 Hom。
使われ方：source frame の同じ右 Quillen 関手。 -/
lemma strictRawModuleSemifree_hom_fibration (X : (operad A).Algebra)
    {P M N : strictRawModuleCategory A X}
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P)
    (p : M ⟶ N) (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A ((strictRawModuleUnderlying X).map p)) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (eHomWhiskerLeft (Complex A) P p) := by
  let D := dgAlgebraCategory A ((assocForget A).obj X)
  have hs : moduleDegreewiseSurjective A D p := by
    intro x
    have hx : x = op DGAlgebraPoint.star := Subsingleton.elim _ _
    subst x
    exact hp
  obtain ⟨F⟩ := hP
  intro n
  exact moduleSemifreeFiltration_postcompose_surjective A D F p hs n

/-- 概要：元の半自由加群からの同じ全 Hom 関手は実モデルで右 Quillen。
方針：同じ次数別全射保存と擬同型保存を二条件へ渡す。
規約：Keller Theorem 3.2 (1)、両モデル構造は実際に構成済み。
使われ方：同じ加群 source frame のテンソル随伴。 -/
lemma strictRawModuleSemifree_hom_isRightQuillen (X : (operad A).Algebra)
    (P : strictRawModuleCategory A X)
    (hP : moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X)) P) :
    letI := strictRawModuleModelCategory A X
    letI := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    SerrePositivity.Quillen.IsRightQuillen
      ((eHomFunctor (Complex A) (strictRawModuleCategory A X)).obj (op P)) := by
  let := strictRawModuleModelCategory A X
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  constructor
  · intro M N p hp
    exact strictRawModuleSemifree_hom_fibration A X hP p hp
  · intro M N p hp
    refine ⟨strictRawModuleSemifree_hom_fibration A X hP p hp.1, ?_⟩
    apply moduleSemifree_postcompose_quasiIso A
      (dgAlgebraCategory A ((assocForget A).obj X)) hP p
    exact (strictRawModuleModelCategory_weakEquivalences A X) ▸ hp.2

end SerrePositivity.EInfinity.BarrattEccles
