module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalAlgebraCartesianComparison
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraCartesianIsomorphism
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleProjectiveEnhancement

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の元の例外因子模型の対象条件。
方針：指定導来比較の可逆性と元の局所 Koszul 模型の perfect 性を全包含で要求する。
規約：正規表示での条件との一致は指定比較射の随伴計算で証明する。
使われ方：例外因子の射影的 dg 候補と共通 Koszul 表示との比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：元の例外因子模型で全包含の canonical な比較が可逆である条件。
方針：実際の導来延長–制限随伴から構成した指定射を使う。
規約：KST §3.1・Lemma 3.6。使われ方：元の模型の cartesian 対象条件。 -/
def exceptionalDiagramCartesian (a : I → R) :
    ObjectProperty (DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :=
  fun X => ∀ (T U : FiniteOverlapIndex I) (h : T ≤ U),
    IsIso (finiteOverlapExceptionalDerivedExtensionComparison R a h X)

/-- 概要：元の例外因子の各局所 Koszul 模型で perfect である条件。
方針：指定局所埋め込みに沿う実際の導来評価を使う。
規約：KST Lemma 3.6。使われ方：元の模型の局所有限性。 -/
def exceptionalDiagramLocallyPerfect (a : I → R) :
    ObjectProperty (DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :=
  fun X => ∀ T : FiniteOverlapIndex I,
    modulePerfect R (FiniteOverlapExceptionalVertexObject R a T)ᵒᵖ
      ((finiteOverlapExceptionalDerivedModuleEvaluation R a T).obj X)

/-- 概要：元の例外因子模型で cartesian かつ局所 perfect な導来対象。
方針：指定された二条件の連言を取る。
規約：KST §3.1・Lemma 3.6。使われ方：例外因子の大域 Perf 候補。 -/
def exceptionalDiagramCartesianPerfect (a : I → R) :
    ObjectProperty (DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :=
  fun X => exceptionalDiagramCartesian R a X ∧ exceptionalDiagramLocallyPerfect R a X

/-- 概要：正規表示と元の例外因子模型の cartesian 条件は一致する。
方針：全包含の指定係数拡大比較の可逆性の iff を全称化する。
規約：KST §3.1・Lemma 3.6。使われ方：元の模型への条件の移送。 -/
theorem finiteOverlapExceptionalAlgebraCartesian_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    diagramAlgebraCartesian (finiteOverlapExceptionalDGAlgebraDiagram R a) X ↔
      exceptionalDiagramCartesian R a X :=
  forall_congr' (fun T => forall_congr' (fun U => forall_congr' (fun h =>
    (finiteOverlapExceptionalAlgebraDerivedExtensionComparison_isIso_iff R a
      (T := T) (U := U) h X).symm)))

/-- 概要：正規表示と元の例外因子模型の局所 perfect 条件は一致する。
方針：各頂点の指定導来評価と Morita 判定の iff を全称化する。
規約：KST Lemma 3.6。使われ方：元の模型への局所有限性の移送。 -/
theorem finiteOverlapExceptionalAlgebraLocallyPerfect_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    diagramAlgebraLocallyPerfect (finiteOverlapExceptionalDGAlgebraDiagram R a) X ↔
      exceptionalDiagramLocallyPerfect R a X :=
  forall_congr' (fun T => finiteOverlapExceptionalAlgebraPerfect_iff R a T X)

/-- 概要：正規表示と元の例外因子模型の cartesian perfect 条件は一致する。
方針：二つの指定比較の iff を組み合わせる。
規約：KST §3.1・Lemma 3.6。使われ方：大域候補の対象条件の比較。 -/
theorem finiteOverlapExceptionalAlgebraCartesianPerfect_iff (a : I → R)
    (X : DerivedAllDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) :
    diagramAlgebraCartesianPerfect (finiteOverlapExceptionalDGAlgebraDiagram R a) X ↔
      exceptionalDiagramCartesianPerfect R a X :=
  and_congr (finiteOverlapExceptionalAlgebraCartesian_iff R a X)
    (finiteOverlapExceptionalAlgebraLocallyPerfect_iff R a X)

/-- 概要：二表示の cartesian perfect 対象性質は等しい。
方針：全対象の iff に関数・命題外延性を適用する。
規約：KST §3.1。使われ方：指定充満部分圏の比較を移す。 -/
theorem finiteOverlapExceptionalAlgebraCartesianPerfect_eq (a : I → R) :
    diagramAlgebraCartesianPerfect (finiteOverlapExceptionalDGAlgebraDiagram R a) =
      exceptionalDiagramCartesianPerfect R a :=
  funext (fun X => propext (finiteOverlapExceptionalAlgebraCartesianPerfect_iff R a X))

/-- 概要：元の例外因子模型の対象条件は導来同型で不変。
方針：正規表示との対象性質の等号で既存の不変性を移す。
規約：KST §3.1・Lemma 3.6。使われ方：射影的代表の選択。 -/
instance exceptionalDiagramCartesianPerfectClosedUnderIso (a : I → R) :
    (exceptionalDiagramCartesianPerfect R a).IsClosedUnderIsomorphisms := by
  rw [← finiteOverlapExceptionalAlgebraCartesianPerfect_eq]
  infer_instance

/-- 概要：元の例外因子模型の二条件を満たす射影的図式加群。
方針：指定主導来像に cartesian perfect 条件を課す。
規約：KST §3.1。使われ方：全次数の導来 Hom を保持する候補対象。 -/
def projectiveExceptionalDiagramCartesianPerfect (a : I → R)
    (M : ProjectiveDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a)) : Prop :=
  exceptionalDiagramCartesianPerfect R a
    ((moduleToDerived R
      (DiagramModuleCoefficientObject (finiteOverlapExceptionalDGAlgebraDiagram R a))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) M.val))

/-- 概要：例外因子の cartesian perfect 射影的 dg 候補模型。
方針：全図式の射影的 dg 加群の Hom を変えずに対象を制限する。
規約：KST §3.1・Lemma 3.6、層の降下比較は別義務。
使われ方：半直交分解に向けた元の局所 Koszul 表示の大域候補。 -/
abbrev ExceptionalCartesianPerfectDiagramDGModel (a : I → R) :=
  DGFullSubcategory (ProjectiveDiagramModules (finiteOverlapExceptionalDGAlgebraDiagram R a))
    (projectiveExceptionalDiagramCartesianPerfect R a)

end SerrePositivity.KST.DerivedBlowup
