module

public import SerrePositivity.KST.Fibration.Relative.ClosedStableFiber
public import SerrePositivity.KST.Fibration.ClosedFlagPostCartesian

/-!
概要：閉じた安定部分圏の元の実 fiber 同型と射影公式を無条件で公開する。
方針：K-B の全旗自然性定理を既存の条件付き後段へ代入する。
規約：入力は B と P のみ。使われ方：K-cof・K-B の第 I 段の接続。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の定数旗四角形は B・P のみから homotopy pullback。
方針：全旗自然性の実定理を Segal 実現へ渡す。
規約：追加の Prop 引数なし。使われ方：無条件の実現四角形。 -/
theorem closedRelativeSquare_homotopyPullback_unconditional
    {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    IsHomotopyPullback (closedRelativeSquare P) :=
  closedRelativeSquare_homotopyPullback P (closedStableFlagPostPullback P)

/-- 概要：F(P) は元の c_B の指定零旗上の homotopy fiber に局所化同型。
方針：既存の指定点基底変換同型の唯一の条件を実定理で放電する。
規約：F は coreSRealizationFunctor、入力は B・P のみ。
使われ方：K-cof・K-B が消費する無条件 S1 同型。 -/
def closedRelativeFiberIso_unconditional
    {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj (closedStableModel P)) ≅
      AnodyneHomotopy.anodyneQ.obj (closedRelativeFiber P) :=
  closedRelativeFiberIso P (closedStableFlagPostPullback P)

/-- 概要：無条件同型の順射と元の fiber 射影の合成は F が送る P 包含。
方針：同じ条件を放電した既存の射影公式。
規約：元の c_B・指定点・包含を保持。使われ方：fiber 列の第一射の同定。 -/
theorem closedRelativeFiberIso_unconditional_projection
    {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (closedRelativeFiberIso_unconditional P).hom ≫
      AnodyneHomotopy.anodyneQ.map (closedRelativeFiberProjection P) =
        AnodyneHomotopy.anodyneQ.map
          (coreSRealizationFunctor.map (closedStableInclusion P)) :=
  closedRelativeFiberIso_projection P (closedStableFlagPostPullback P)

/-- 概要：元の包含と c_B の合成を指定零旗へ零化する実ホモトピー。
方針：既存の可縮全旗による指定点ホモトピーをそのまま公開する。
規約：入力は B・P のみ、標的は元の相対実現の Ex∞。
使われ方：無条件 fiber 列の零化データ。 -/
def closedRelativeNullhomotopy_unconditional
    {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    SSet.Homotopy
      (stdSimplex.isTerminalObj₀.from (coreSRealizationFunctor.obj (closedStableModel P)) ≫
        closedRelativeBasepoint P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedRelativeRealization P))
      (coreSRealizationFunctor.map (closedStableInclusion P) ≫ closedRelativeConstant P ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedRelativeRealization P)) :=
  closedRelativeNullhomotopy P

end SerrePositivity.KST.Fibration.Relative
