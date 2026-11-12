module

public import SerrePositivity.EInfinity.BarrattEccles.MappingResolutionCofinality
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceSpanDiagram
public import SerrePositivity.EInfinity.FrameHom.ResolutionFixedRightComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CostructuredArrowPreDiagram
public import SerrePositivity.EInfinity.FrameHom.FixedRightGrothendieckInversion

/-!
# 実際の E 代数の全固定右脚の比較と右変数の自然性

概要：同じ Map^h の分解を使い、全右対象で元の比較の余終性を証明する。
方針：同じ転送モデルと分解を局所代入し、全右脚上の自然変換へ束ねる。
規約：元の代数の cofibrancy・右対象の fibrancy・単体集合モデルを入力しない。
使われ方：三本矢の全図式への成分ごとの余終性の具体的な入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

/-- 概要：実際の各右対象で同じ分解から全左脚への比較（Low 命題 3.7）。
方針：同じ mappingCofibrantFactorization の元の比較関手を使う。
規約：元の右対象の同じ up を使う。
使われ方：全右脚の図式の成分ごとの比較。 -/
abbrev mappingResolutionFixedRightComparison (X V : (operad A).Algebra) :=
  let := modelCategory A
  FrameHom.resolutionFixedRightComparison.{u + 1, u, u + 1}
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X) V

/-- 概要：実際の分解の比較は全固定右対象で left cofinal（Low 命題 3.7）。
方針：同じ分解の余終性を元の right fibration に沿って引き戻す。
規約：任意の可換環・元の任意の代数を扱う。
使われ方：三本矢の全図式の各成分の比較。 -/
lemma mappingResolutionFixedRightComparison_isLeftCofinal (X V : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (mappingResolutionFixedRightComparison A X V)) := by
  let := modelCategory A
  exact FrameHom.resolutionFixedRightComparison_isLeftCofinal _ V

/-- 概要：実際の各固定右対象の元の比較は弱ホモトピー同値（Low 命題 3.7）。
方針：同じ比較射の余終性を全 Kan 標的で検査する。
規約：元の nerve の両端に Kan 性を要求しない。
使われ方：全図式の成分ごとのホモトピー型の比較。 -/
lemma mappingResolutionFixedRightComparison_isWeakHomotopyEquivalence
    (X V : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (mappingResolutionFixedRightComparison A X V)) :=
  (mappingResolutionFixedRightComparison_isLeftCofinal A X V).isWeakHomotopyEquivalence

/-- 概要：元の E 代数の固定右対象の比較は anodyne 反転後に可逆（Low 命題 3.7）。
方針：同じ分解の元の比較の余終性をそのまま反転する。
規約：基礎環・元の代数に追加仮定を要求しない。
使われ方：三本矢の全図式の各成分の同じ反転性。 -/
lemma mappingResolutionFixedRightComparison_localized_isIso (X V : (operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (mappingResolutionFixedRightComparison A X V))) :=
  FrameHom.leftCofinal_localized_isIso _ (mappingResolutionFixedRightComparison_isLeftCofinal A X V)

/-- 概要：全右脚の元の終域の射影を同じ小圏へ送る（Low 命題 3.7）。
方針：元の右脚の slice の終域射影の前後で up・down を行う。
規約：全ての元の右脚と全ての遷移を保持する。
使われ方：右変数の全 Cat 値図式の自然性。 -/
def mappingSmallRightSpanForget (Y : (operad A).Algebra) :
    AsSmall.{u + 1} (algebraRightSpanBase A Y) ⥤ AsSmall.{u + 1} (operad A).Algebra := by
  let := modelCategory A
  exact AsSmall.down ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowSpanComma.rightSliceForget (trivialCofibrations (operad A).Algebra) Y ⋙
      AsSmall.up

/-- 概要：元の全固定右脚の比較を全右脚の図式へ自然に束ねる（Low 命題 3.7）。
方針：元の前合成と後合成の厳密な交換を同じ右脚の射影に沿って制限する。
規約：元の比較の各成分と全係数射を保持する。
使われ方：三本矢の全図式の比較の自然変換。 -/
abbrev mappingFixedRightDiagramComparison (X Y : (operad A).Algebra) :=
  let := modelCategory A
  Functor.whiskerLeft (mappingSmallRightSpanForget A Y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagramPre (mappingSmallResolutionOverFunctor A X)
      (FrameHom.smallResolutionLeftForget.{u + 1, u, u + 1} X))

/-- 概要：同じ全右脚の自然変換の全成分は left cofinal（Low 命題 3.7）。
方針：元の右対象ごとの比較の余終性を同じ成分で使う。
規約：全ての自明 cofibration の右脚を含む。
使われ方：全図式の比較への成分ごとの余終性の入力。 -/
lemma mappingFixedRightDiagramComparison_isLeftCofinal (X Y : (operad A).Algebra)
    (t : AsSmall.{u + 1} (algebraRightSpanBase A Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap ((mappingFixedRightDiagramComparison A X Y).app t).toFunctor) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagramPre_isLeftCofinal _ _
    (mappingSmallResolutionOverFunctor_isLeftCofinal A X) ((mappingSmallRightSpanForget A Y).obj t)

/-- 概要：全右脚の同じ自然変換の全成分は anodyne 反転後に可逆（Low 命題 3.7）。
方針：元の各成分の余終性を同じ射の反転性へ移す。
規約：全ての右脚と全ての係数射に自然な元の比較を使う。
使われ方：全図式の比較へ成分ごとの反転性を適用する。 -/
lemma mappingFixedRightDiagramComparison_localized_isIso (X Y : (operad A).Algebra)
    (t : AsSmall.{u + 1} (algebraRightSpanBase A Y)) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap ((mappingFixedRightDiagramComparison A X Y).app t).toFunctor)) :=
  FrameHom.leftCofinal_localized_isIso _ (mappingFixedRightDiagramComparison_isLeftCofinal A X Y t)

/-- 概要：元の分解から全左脚への右変数の全図式の比較（Low 命題 3.7）。
方針：同じ自然変換を Grothendieck 構成で送る。
規約：反転性は全 comma の収縮で別途証明し、成分の結論から省略しない。
使われ方：元の三本矢の全図式への比較の適用先。 -/
abbrev mappingFixedRightGrothendieckComparison (X Y : (operad A).Algebra) :=
  let := modelCategory A
  Grothendieck.map (mappingFixedRightDiagramComparison A X Y)

/-- 概要：実際の E 代数の全図式の同じ比較は anodyne 反転後に可逆（Low 命題 3.7）。
方針：元の分解の余終性と全 comma の明示的な収縮を同じモデルへ局所代入する。
規約：元の代数に cofibrancy や単体集合モデルを要求しない。
使われ方：分解から全左脚への元の全右脚の図式の比較の反転。 -/
lemma mappingFixedRightGrothendieckComparison_localized_isIso (X Y : (operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (mappingFixedRightGrothendieckComparison A X Y))) := by
  let := modelCategory A
  exact FrameHom.fixedRightGrothendieckComparison_localized_isIso
    (mappingSmallResolutionOverFunctor A X)
    (FrameHom.smallResolutionLeftForget.{u + 1, u, u + 1} X)
    (mappingSmallRightSpanForget A Y) (mappingSmallResolutionOverFunctor_isLeftCofinal A X)

/-- 概要：元の全図式の比較は弱ホモトピー同値（Low 命題 3.7）。
方針：元の同じ射の anodyne 反転後の可逆性を全 Kan 標的で検査する。
規約：元の二つの全図式の nerve の Kan 性を要求しない。
使われ方：三本矢の全図式の元の比較のホモトピー型。 -/
lemma mappingFixedRightGrothendieckComparison_isWeakHomotopyEquivalence
    (X Y : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (mappingFixedRightGrothendieckComparison A X Y)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (mappingFixedRightGrothendieckComparison_localized_isIso A X Y)

end SerrePositivity.EInfinity.BarrattEccles
