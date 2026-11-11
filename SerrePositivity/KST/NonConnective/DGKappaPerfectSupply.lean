module
public import SerrePositivity.InfinityCategories.Project.Entrypoints.DerivedKappaPerfectAll
public import SerrePositivity.KST.NonConnective.DGSuspensionPerfectConnectiveSequence
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeStageFamily

/-!
概要：D-8 e の実供給を同じ I に代入し、P を独立入力にしない反復懸垂の入口を作る。
方針：正本の dgKappaPerfectInput を元の各 cone へ適用し、既存の段・列を使う。
規約：I 自体・全高次作用・構造辺の自然性は未供給のまま。元の κ と cone を変更しない。
使われ方：K-7 c5・d の実 Perf 比較と反復列から独立した P 入力を除く。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}

/-- 概要：同じ明示 cone I から、D-8 e が P を供給する元の段入力を作る。
方針：D 正本の三フィールドの実構成を同じ I に適用する。
規約：I の存在を主張せず、cone を選び直さない。
使われ方：P の独立供給を要しない反復懸垂の入口。 -/
def dgKappaSuppliedStageInput (A : PerfDGInput.{u, max (u + 1) v} R)
    (I : DGKappaConeInput R A κ) : DGSuspensionStageInput R κ A where
  cone := I
  perfect := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R A I

/-- 概要：P を実供給しても、元の段の cone は同じ I そのもの。
方針：元の段入力の射影を計算する。
規約：κ-compact 模型を別の選択へ置換しない。
使われ方：既存の商・零角・BF 列との厳密照合。 -/
theorem dgKappaSuppliedStageInput_cone (A : PerfDGInput.{u, max (u + 1) v} R)
    (I : DGKappaConeInput R A κ) : (dgKappaSuppliedStageInput R A I).cone = I := rfl

/-- 概要：各元の入力への cone 供給だけから、同じ P 実供給を持つ全段入力を作る。
方針：各 I を変更せず、D-8 e の元の実構成を適用する。
規約：cone 供給の存在・入力射作用・全高次自然性は主張しない。
使われ方：K-7 の既存の反復列・比較の全利用側へ同じ供給を代入する。 -/
def dgKappaSuppliedStageProvider
    (I : ∀ A : PerfDGInput.{u, max (u + 1) v} R, DGKappaConeInput R A κ) :
    DGSuspensionStageProvider.{u, v} R κ :=
  fun A => dgKappaSuppliedStageInput R A (I A)

/-- 概要：I だけに条件付きで、同じ実小核への固定 ν の Perf 同値を供給する。
方針：実評価 Morita 比較の既存入口へ D-8 e の同じ P を代入する。
規約：全入力自然性を対象別の同値から推論しない。
使われ方：K-7 c5 の独立した P・Perf 同値入力を要しない入口。 -/
def dgKappaSuppliedKernelPerfEquivalence (A : PerfDGInput.{u, max (u + 1) v} R)
    (I : DGKappaConeInput R A κ) :=
  dgKappaResolvedKernelPerfEquivalence R A I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R A I)

/-- 概要：同じ cone 供給と零所属だけに条件付きで、元の実反復 BF 列を得る。
方針：同じ各 I と D-8 e の P を保持する段入力を既存の列へ渡す。
規約：I・零所属・連結版 K-6・全入力自然性の供給を完成扱いしない。
使われ方：K-7 c5・d の P を独立仮定にしない同じ実非連結化列。 -/
def dgSuspensionSuppliedPerfectConnectiveSequence
    (I : ∀ A : PerfDGInput.{u, max (u + 1) v} R, DGKappaConeInput R A κ)
    (A : PerfDGInput.{u, max (u + 1) v} R)
    (Z : ∀ n, DGKappaZeroInput R
      (dgSuspensionIteration R (dgKappaSuppliedStageProvider R I) A n)
      (dgSuspensionIterationStage R (dgKappaSuppliedStageProvider R I) A n).cone) :=
  dgSuspensionPerfectConnectiveSequence R (dgKappaSuppliedStageProvider R I) A Z

/-- 概要：既存の段供給の P を実供給へ差し替えても、反復する同じ dg 入力は変わらない。
方針：各段の元の cone を保ち、同じ商入力を再帰的に照合する。
規約：元の P との全入力比較や構造射の等号を対象の等号から推論しない。
使われ方：D-8 e の消費で既存の反復対象を選び直さないことの確認。 -/
theorem dgKappaSuppliedIteration_eq
    (s : DGSuspensionStageProvider.{u, v} R κ)
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    dgSuspensionIteration R (dgKappaSuppliedStageProvider R (fun B => (s B).cone)) A n =
      dgSuspensionIteration R s A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun B : PerfDGInput.{u, max (u + 1) v} R =>
      dgKappaSuspensionKInput R B (s B).cone) ih

/-- 概要：既存の全高次懸垂作用を、同じ cone と実供給 P の段入力へそのまま移す。
方針：元の全単体写像・頂点・元の実入力射・全一単体を再利用する。
規約：全高次作用の存在は明示入力のまま。P の実供給から作用の存在を推論しない。
使われ方：D-8 e を消費しても元の同じ全 native 作用を保持する。 -/
def dgKappaSuppliedNativeAction
    (s : DGSuspensionStageProvider.{u, v} R κ) (a : DGSuspensionNativeActionInput R s) :
    DGSuspensionNativeActionInput R
      (dgKappaSuppliedStageProvider R (fun B => (s B).cone)) where
  map := a.map
  vertex := a.vertex
  data := a.data
  edge := a.edge

/-- 概要：P の実供給への差し替えは元の全高次懸垂写像を厳密に保つ。
方針：同じ実入力の全単体写像の射影を計算する。
規約：点別の比較だけへ弱めない。
使われ方：元の全 native 入力作用を選び直さないことの照合。 -/
theorem dgKappaSuppliedNativeAction_map
    (s : DGSuspensionStageProvider.{u, v} R κ) (a : DGSuspensionNativeActionInput R s) :
    (dgKappaSuppliedNativeAction R s a).map = a.map := rfl

/-- 概要：P の実供給へ差し替えた後も、各段の全入力 K・native loop 族は元の同じ族。
方針：同じ懸垂写像の同じ回数の反復と固定 K の合成を展開する。
規約：構造辺 β の自然性は主張せず、構成済みの各段族だけを厳密照合する。
使われ方：K-7 c4・c5 の P 実供給と元の全高次段族の整合。 -/
theorem dgKappaSuppliedNativeStageFamily_eq
    (s : DGSuspensionStageProvider.{u, v} R κ) (a : DGSuspensionNativeActionInput R s) (n : ℕ) :
    dgSuspensionNativeStageFamily R
        (dgKappaSuppliedStageProvider R (fun B => (s B).cone))
        (dgKappaSuppliedNativeAction R s a) n = dgSuspensionNativeStageFamily R s a n := rfl

end SerrePositivity.KST.NonConnective
