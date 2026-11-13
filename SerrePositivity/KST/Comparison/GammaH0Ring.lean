module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Comparison.GammaZeroRing
public import SerrePositivity.KST.Comparison.DGAlgebra

/-!
# Γ の H⁰ 比較の乗法性

概要：Γ の連結成分から H⁰ の自己射への写像を環として比較する。
方針：零単体での閉射の同定を使い、加法・積を代表元で計算する。
規約：SS03 (2.9) の AW 積と KST 式 (2.2) の成分環。
使われ方：dg 代数の π₀A を H⁰(A) として読むための比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory DifferentialGraded

open scoped Simplicial

variable {R : Type u} [CommRing R] {D : Type u} [DGCategory R D]

/--
概要：Γ から pinched Hom への同型は零次で通常の閉零射に一致する。
方針：標準座標の次数零の符号を消し、既存の再構成の閉成分を評価する。
規約：SS03 (2.9) の零次部分の同定。
使われ方：H⁰ 比較の加法性・乗法性を代表元で証明する。
-/
theorem gammaEndPinched_vertex (x : D) (s : GammaEnd (R := R) x 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexClosedEquiv x x
      ((gammaEndPinchedIso (R := R) x).hom.app _ s) =
        (gammaZeroClosedRingEquiv (R := R) x s).asHom := by
  apply (closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
    (ForgetEnrichment.of (Complex R) x)).injective
  let p := (gammaEndPinchedIso (R := R) x).hom.app (Opposite.op ⦋0⦌) s
  let e := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) p).toTruncated)
  let c := closedHomEquiv R D (ForgetEnrichment.of (Complex R) x)
    (ForgetEnrichment.of (Complex R) x)
  change c (c.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e)) =
    c (c.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x x s))
  rw [c.apply_symm_apply, c.apply_symm_apply]
  apply Subtype.ext
  apply eq_of_heq
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle
  refine (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.castCycle_val_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e) _).trans ?_
  let l := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv (R := R) x x 0).symm s
  change HEq (l.val.toSimplexData.hom {0, 1} 0 1 0 (by decide) (by decide) (by decide)
    (by decide)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval x x s).val
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.toSimplexData_hom_last
    l.val ({0, 1} : Finset (Fin 2)) 0 1 0 (by decide) (by decide) (by decide) (by decide) rfl
  refine h.trans ?_
  apply heq_of_eq
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData s.val).component _ 0 (by decide) (by decide) =
    s.val.component Finset.univ 0 Finset.univ_nonempty (by simp)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.signChangeData_component]
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast
      ({0, 1} : Finset (Fin 2)) = ({0} : Finset (Fin 1)) := by decide
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign, hw]

/--
概要：Γ の H⁰ 比較は零単体を閉零射の境界類へ送る。
方針：π₀ の誘導写像を代表元で評価して零次の閉射の計算を使う。
規約：SS03 (2.9)、KST §2.2 の成分環の標準写像。
使われ方：環の演算の保存の代表元での証明。
-/
theorem gammaEndPiZeroH0Equiv_mk (x : D) (s : GammaEnd (R := R) x 0) :
    gammaEndPiZeroH0Equiv (R := R) x (SSet.π₀.mk s) =
      (toHomotopy R D).map (gammaZeroClosedRingEquiv (R := R) x s).asHom := by
  change (toHomotopy R D).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexClosedEquiv x x
      ((gammaEndPinchedIso (R := R) x).hom.app _ s)) = _
  rw [gammaEndPinched_vertex]

/--
概要：Γ の連結成分環は dg 圏の H⁰ の自己射環と同型である。
方針：台の全単射に対し、零次単体の代表で加法と AW 積を計算する。
規約：H⁰ の環構造は既存のホモトピー圏の End の構造。輸送で置き換えない。
使われ方：SS03 Proposition 2.13 と KST 式 (2.2) の π₀A = H⁰(A)。
-/
def gammaEndH0RingEquiv (x : D) :
    SSet.π₀ (ringSpace (gammaEndRingObject (R := R) x)) ≃+*
      End ((toHomotopy R D).obj (ForgetEnrichment.of (Complex R) x)) where
  toEquiv := (gammaEndPiZeroH0Equiv (R := R) x).trans End.homEquiv.symm
  map_add' a b := by
    induction a using SSet.π₀.rec with | mk a => ?_
    induction b using SSet.π₀.rec with | mk b => ?_
    apply End.ext
    change gammaEndPiZeroH0Equiv x (SSet.π₀.mk (a + b)) =
      gammaEndPiZeroH0Equiv x (SSet.π₀.mk a) + gammaEndPiZeroH0Equiv x (SSet.π₀.mk b)
    rw [gammaEndPiZeroH0Equiv_mk, gammaEndPiZeroH0Equiv_mk, gammaEndPiZeroH0Equiv_mk,
      map_add (gammaZeroClosedRingEquiv (R := R) x)]
    exact (toHomotopy R D).map_add
  map_mul' a b := by
    induction a using SSet.π₀.rec with | mk a => ?_
    induction b using SSet.π₀.rec with | mk b => ?_
    apply End.ext
    change gammaEndPiZeroH0Equiv x (SSet.π₀.mk (a * b)) =
      gammaEndPiZeroH0Equiv x (SSet.π₀.mk b) ≫ gammaEndPiZeroH0Equiv x (SSet.π₀.mk a)
    rw [gammaEndPiZeroH0Equiv_mk, gammaEndPiZeroH0Equiv_mk, gammaEndPiZeroH0Equiv_mk,
      map_mul (gammaZeroClosedRingEquiv (R := R) x)]
    exact (toHomotopy R D).map_comp _ _

/--
概要：一対象 dg 代数の H⁰ を既存のホモトピー圏の自己射環として取る。
方針：閉零射を境界関係で割った既存の圏の End を使う。
規約：新しい環演算を仮定しない。KST §2.2 の離散係数環。
使われ方：ΓA の成分環との比較先。
-/
def dgAlgebraH0Ring (A : DGAlgebraModel R) : RingCat.{u} := by
  letI := A
  exact RingCat.of (End ((toHomotopy R PUnit).obj
    (ForgetEnrichment.of (Complex R) PUnit.unit)))

/--
概要：dg 代数の Γ の成分環は H⁰ の環と同型である。
方針：自己 Hom の環比較を一対象 dg 圏に適用する。
規約：SS03 Proposition 2.13、KST 式 (2.2)。cochain 規約の零次ホモロジー。
使われ方：低次数 K 群の比較における π₀A の同定。
-/
def dgAlgebraComponentsH0RingEquiv (A : DGAlgebraModel R) :
    dgAlgebraComponents R A ≃+* dgAlgebraH0Ring A := by
  letI := A
  exact gammaEndH0RingEquiv (R := R) PUnit.unit

end SerrePositivity.KST.Comparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.4.4" (partial := component) "仮定：可換環 R 上の一対象 dg 圏としての dg 代数（HA と一致する dg 模型）。結論：閉零射を境界で割った H⁰ に自己射の合成による環構造を与える（零次の環の部分に一致）。全次数の次数付き R 代数と擬同型による全次数の環同型の判定は含まれない。"] _root_.SerrePositivity.KST.Comparison.dgAlgebraH0Ring
