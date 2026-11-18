module

public import SerrePositivity.DifferentialGraded.Algebras.AWIntervalComonoid
public import SerrePositivity.DifferentialGraded.Algebras.ConvolutionNaturality
public import SerrePositivity.DifferentialGraded.Algebras.ConvolutionUnitComparison
public import SerrePositivity.DifferentialGraded.Algebras.PathInput
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.HomologicalAlgebra.Complexes.HomHomotopy
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IntervalEvaluationFibration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：実 AW 区間上の畳み込み dg 代数を path object にする。
方針：余単位を定数射、二つの余モノイド端点を評価射へ転置する。
規約：底は Hom(N(Δ¹),B) で、大域モデル構造を使わない。
使われ方：自由 dg 代数の右転送の実 acyclicity 入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial _root_.CategoryTheory.ComonObj
variable (R : Type u) [CommRing R]

local instance _root_.SerrePositivity.DGAlgebra.instHasBinaryProductsComplex : HasBinaryProducts (Complex R) :=
  (_root_.SerrePositivity.ProjectiveModel.projectiveModelCategory R).cm1a.out (Discrete WalkingPair)

attribute [local instance] _root_.SerrePositivity.DGAlgebra.hasBinaryProducts _root_.SerrePositivity.DGAlgebra.hasTerminal

/-- 概要：単位余モノイド上の畳み込みの定数射の底。
方針：余単位が恒等射であることを使う。
規約：元の単位内部 Hom 比較。使われ方：端点評価の終域の比較。 -/
lemma convolutionUnitMap_trivial_hom (B : Mon (Complex R)) :
    (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B).hom =
      (MonoidalClosed.unitNatIso (C := Complex R)).hom.app B.X := by
  change _root_.SerrePositivity.DGAlgebra.convolutionUnitHom R (Comon.trivial (Complex R)) B = _
  rw [_root_.SerrePositivity.DGAlgebra.convolutionUnitHom_unit_pre]
  change _ ≫ (MonoidalClosed.pre (𝟙 (𝟙_ (Complex R)))).app B.X = _
  rw [MonoidalClosed.pre_id]
  exact Category.comp_id _

/-- 概要：単位余モノイド上の畳み込みは元の代数と同型。
方針：底の単位比較の同型性を反映する。
規約：局所で使う IsIso。使われ方：二端点の評価代数射。 -/
lemma convolutionUnitMap_trivial_isIso (B : Mon (Complex R)) :
    IsIso (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B) := by
  have : IsIso (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B).hom := by
    rw [_root_.SerrePositivity.DGAlgebra.convolutionUnitMap_trivial_hom]
    infer_instance
  have : IsIso ((Mon.forget (Complex R)).map
      (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B)) := ‹_›
  exact isIso_of_reflects_iso _ (Mon.forget (Complex R))

/-- 概要：実 AW 区間の端点評価を dg 代数射にする。
方針：余モノイド射による前合成と単位畳み込みの逆比較を合成する。
規約：false と true は元の区間の端点。使われ方：実 path object。 -/
def awEvaluation (B : Mon (Complex R)) (b : Bool) :
    (_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1])).obj B ⟶ B := by
  have := _root_.SerrePositivity.DGAlgebra.convolutionUnitMap_trivial_isIso R B
  exact _root_.SerrePositivity.DGAlgebra.convolutionRestriction R (_root_.SerrePositivity.DGAlgebra.intervalEndpointComon R b) B ≫
    inv (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B)

/-- 概要：代数の端点評価の底は既存の複体の端点評価。
方針：単位比較の逆と閉構造の前合成を照合する。
規約：元の複体射の等式。使われ方：擬同型性と二端点全射性の再利用。 -/
lemma awEvaluation_hom (B : Mon (Complex R)) (b : Bool) :
    (_root_.SerrePositivity.DGAlgebra.awEvaluation R B b).hom = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).evaluation B.X b := by
  have := _root_.SerrePositivity.DGAlgebra.convolutionUnitMap_trivial_isIso R B
  change (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.endpoint R b)).app B.X ≫
    (inv (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B)).hom = _
  rw [_root_.SerrePositivity.ComplexLimits.complexClosed_pre]
  congr 1
  have h := (Mon.forget (Complex R)).map_inv
    (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B)
  change (inv (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B)).hom =
    inv (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (Comon.trivial (Complex R)) B).hom at h
  rw [h]
  apply IsIso.inv_eq_of_hom_inv_id
  erw [_root_.SerrePositivity.DGAlgebra.convolutionUnitMap_trivial_hom]
  exact (MonoidalClosed.unitNatIso (C := Complex R)).hom_inv_id_app B.X

/-- 概要：AW 定数射の底は既存の区間の定数射。
方針：余単位による前合成の照合を使う。
規約：同じ収縮を保持する。使われ方：実際の定数射の擬同型性。 -/
lemma awConstant_hom (B : Mon (Complex R)) :
    (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).constant B.X := by
  change _root_.SerrePositivity.DGAlgebra.convolutionUnitHom R _ B = _
  rw [_root_.SerrePositivity.DGAlgebra.convolutionUnitHom_unit_pre, _root_.SerrePositivity.ComplexLimits.complexClosed_pre]
  rfl

/-- 概要：AW 定数射と端点評価の厳密な三角形。
方針：元の余モノイド端点の前合成の自然性と単位比較を使う。
規約：代数射の等式。使われ方：前 path object の二律。 -/
lemma awConstant_evaluation (B : Mon (Complex R)) (b : Bool) :
    _root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B ≫
      _root_.SerrePositivity.DGAlgebra.awEvaluation R B b = 𝟙 B := by
  apply Mon.Hom.ext'
  change (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B).hom ≫
    (_root_.SerrePositivity.DGAlgebra.awEvaluation R B b).hom = 𝟙 B.X
  rw [_root_.SerrePositivity.DGAlgebra.awConstant_hom, _root_.SerrePositivity.DGAlgebra.awEvaluation_hom]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).constant_evaluation B.X b

/-- 概要：元の AW 区間上の畳み込み dg 代数の前 path object。
方針：同じ定数射と二端点評価を束ねる。
規約：carrier は元の内部 Hom。使われ方：転送 acyclicity の実入力。 -/
def awPrepath (B : Mon (Complex R)) : PrepathObject B where
  P := (_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1])).obj B
  p₀ := _root_.SerrePositivity.DGAlgebra.awEvaluation R B false
  p₁ := _root_.SerrePositivity.DGAlgebra.awEvaluation R B true
  ι := _root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B
  ι_p₀ := _root_.SerrePositivity.DGAlgebra.awConstant_evaluation R B false
  ι_p₁ := _root_.SerrePositivity.DGAlgebra.awConstant_evaluation R B true

/-- 概要：AW 二端点評価の底は二項直和上の既存評価対と比較できる。
方針：忘却による積の比較と直和・積同型を使う。
規約：二つの射影を保持する。使われ方：次数別全射性の移送。 -/
lemma awPrepath_p_compare (B : Mon (Complex R)) :
    (_root_.SerrePositivity.DGAlgebra.awPrepath R B).p.hom ≫ prodComparison (Mon.forget (Complex R)) B B =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).evaluationPair B.X ≫ (biprod.isoProd B.X B.X).hom := by
  apply prod.hom_ext
  · erw [Category.assoc, prodComparison_fst]
    erw [Category.assoc, biprod.isoProd_hom, prod.lift_fst]
    change _ = _ ≫ biprod.fst
    erw [biprod.lift_fst]
    exact (congrArg Mon.Hom.hom (PrepathObject.p_fst (_root_.SerrePositivity.DGAlgebra.awPrepath R B))).trans
      (_root_.SerrePositivity.DGAlgebra.awEvaluation_hom R B false)
  · erw [Category.assoc, prodComparison_snd]
    erw [Category.assoc, biprod.isoProd_hom, prod.lift_snd]
    change _ = _ ≫ biprod.snd
    erw [biprod.lift_snd]
    exact (congrArg Mon.Hom.hom (PrepathObject.p_snd (_root_.SerrePositivity.DGAlgebra.awPrepath R B))).trans
      (_root_.SerrePositivity.DGAlgebra.awEvaluation_hom R B true)

/-- 概要：AW 二端点評価は全次数で全射。
方針：既存の区間境界の cofibration から得た評価対を二つの積比較で移す。
規約：代数の cofibrancy を仮定しない。使われ方：path の持ち上げ。 -/
lemma awPrepath_p_projectiveFibration (B : Mon (Complex R)) :
    _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R (_root_.SerrePositivity.DGAlgebra.awPrepath R B).p.hom := by
  have : PreservesLimitsOfShape (Discrete WalkingPair) (Mon.forget (Complex R)) :=
    CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
      (Mon.forget (Complex R))
  let e : ((B ⨯ B : Mon (Complex R))).X ≅ B.X ⊞ B.X :=
    (asIso (prodComparison (Mon.forget (Complex R)) B B)) ≪≫ (biprod.isoProd B.X B.X).symm
  have h : (_root_.SerrePositivity.DGAlgebra.awPrepath R B).p.hom ≫ e.hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).evaluationPair B.X := by
    change ((_root_.SerrePositivity.DGAlgebra.awPrepath R B).p.hom ≫
      prodComparison (Mon.forget (Complex R)) B B) ≫ (biprod.isoProd B.X B.X).inv = _
    rw [_root_.SerrePositivity.DGAlgebra.awPrepath_p_compare, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh : (_root_.SerrePositivity.DGAlgebra.awPrepath R B).p.hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).evaluationPair B.X ≫ e.inv := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hh]
  intro n
  have : IsIso (e.inv.f n) := by
    change IsIso (((eval (ModuleCat R) (.up ℤ) n).mapIso e).inv)
    infer_instance
  exact ((ModuleCat.epi_iff_surjective _).1 (inferInstance : Epi (e.inv.f n))).comp
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coalgebraInterval R).evaluationPair_projectiveFibration B.X n)

/-- 概要：AW 定数射自身の底は擬同型。
方針：標準単体の余単位の実ホモトピー逆を内部 Hom に移す。
規約：任意の非有界の終域。使われ方：二端点評価の擬同型性。 -/
lemma awConstant_quasiIso (B : Mon (Complex R)) :
    QuasiIso (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B).hom := by
  have : QuasiIso (homPrecompose (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit R Δ[1]) B.X) :=
    (_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyEquiv
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv R ⦋1⦌) B.X).quasiIso_hom
  change QuasiIso (_root_.SerrePositivity.DGAlgebra.convolutionUnitHom R _ B)
  rw [_root_.SerrePositivity.DGAlgebra.convolutionUnitHom_unit_pre, _root_.SerrePositivity.ComplexLimits.complexClosed_pre]
  change QuasiIso ((MonoidalClosed.unitNatIso (C := Complex R)).hom.app B.X ≫
    homPrecompose (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit R Δ[1]) B.X)
  infer_instance

/-- 概要：元の AW 端点評価は底で擬同型。
方針：同じ定数射の擬同型性と厳密な三角形から二対三を使う。
規約：両端点、任意の dg 代数。使われ方：実転送の path 入力。 -/
lemma awEvaluation_quasiIso (B : Mon (Complex R)) (b : Bool) :
    QuasiIso (_root_.SerrePositivity.DGAlgebra.awEvaluation R B b).hom := by
  have := _root_.SerrePositivity.DGAlgebra.awConstant_quasiIso R B
  have h := congrArg Mon.Hom.hom (_root_.SerrePositivity.DGAlgebra.awConstant_evaluation R B b)
  change (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B).hom ≫
    (_root_.SerrePositivity.DGAlgebra.awEvaluation R B b).hom = 𝟙 B.X at h
  have : QuasiIso ((_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B).hom ≫
      (_root_.SerrePositivity.DGAlgebra.awEvaluation R B b).hom) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_left
    (_root_.SerrePositivity.DGAlgebra.convolutionUnitMap R (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainComon R Δ[1]) B).hom
    (_root_.SerrePositivity.DGAlgebra.awEvaluation R B b).hom

/-- 概要：実 AW 畳み込みから転送の path 入力を供給する。
方針：既存の複体評価の擬同型性と上の全射性を束ねる。
規約：追加の仮定と大域 instance はない。使われ方：dg 代数モデル構造。 -/
def awPathInput : _root_.SerrePositivity.DGAlgebra.AWPathInput R where
  path := _root_.SerrePositivity.DGAlgebra.awPrepath R
  carrier _ := Iso.refl _
  pair_fibration := _root_.SerrePositivity.DGAlgebra.awPrepath_p_projectiveFibration R
  first_quasiIso B := by
    change QuasiIso (_root_.SerrePositivity.DGAlgebra.awEvaluation R B false).hom
    exact _root_.SerrePositivity.DGAlgebra.awEvaluation_quasiIso R B false
  second_quasiIso B := by
    change QuasiIso (_root_.SerrePositivity.DGAlgebra.awEvaluation R B true).hom
    exact _root_.SerrePositivity.DGAlgebra.awEvaluation_quasiIso R B true

end SerrePositivity.DGAlgebra
