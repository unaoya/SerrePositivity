module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageGeneratorDifferential
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellularCarrierKFlat
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgExtensionForget

/-!
# Cofibrant 代数の台の K 平坦性と係数拡大の忘却

## 概要
Berger–Moerdijk 命題 4.1 のセル表示で台の K 平坦性を示し、HA §3.2.2 の比較を得る。

## 方針
始対象からの実際のセル段の語の基底を使い、小対象分解と retract へ移す。

## 規約
構成済みの Barratt–Eccles のモデル構造を使い、界面に新しい仮定を加えない。

## 使われ方
M13 の `baseChange_forget` 欄。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra DifferentialGraded SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- A cofibrant Barratt–Eccles algebra has a K-flat underlying complex. -/
lemma cofibrantCarrierKFlat (X : (operad A).Algebra) :
    let := modelCategory A
    IsCofibrant X → complexKFlat A X.carrier := by
  apply cofibrantCarrierKFlat_of_cellStages A ?_ X
  dsimp only
  intro J _ _ _ _ Z W g t hZ j
  exact cellStageCarrierKFlat t hZ j

/-- Each object of the specified cofibrant DK input has K-flat carrier. -/
lemma cofibrantAlgebraDKCarrierKFlat (X : (cofibrantAlgebraRelativeCategory A).category) :
    complexKFlat A ((cofibrantAlgebraDKForget A).obj X) := by
  let := modelCategory A
  exact cofibrantCarrierKFlat A ((cofibrantAlgebraDKInclusion A).obj X)
    (cofibrantAlgebra_isCofibrant A X)

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- HA §3.2.2: algebra base change and underlying derived base change commute naturally. -/
def barrattEcclesBaseChange_forget :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (barrattEcclesBaseChange f ≫ cAlgForgetDerived T)
      (cAlgForgetDerived S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f) :=
  barrattEcclesBaseChange_forget_of_cofibrantCarrierKFlat f (cofibrantAlgebraDKCarrierKFlat S)

end SerrePositivity.EInfinity.BarrattEccles
