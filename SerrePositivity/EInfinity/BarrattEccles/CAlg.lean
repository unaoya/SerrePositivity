module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantDiscreteAlgebra
public import SerrePositivity.EInfinity.SimplicialLocalization.Nerve

/-!
# Cofibrant E 代数の具体的な coherent nerve としての CAlg_R

概要：任意の可換環上の具体的な E 代数相対圏から CAlg_R を構成する。
方針：自由単体的局所化・同じ Ex∞ Kan 化・coherent nerve を適用する。
規約：Map^h の高次比較・忘却の ∞ 関手化・極限保存は後続で証明する。
使われ方：E2b の CAlg_R と元の E 代数・離散対象の頂点。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open SerrePositivity.EInfinity.SimplicialLocalization
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：CAlg_R のための具体的な局所 Kan な単体的圏（Dwyer–Kan）。
方針：cofibrant E 代数の実際の相対圏へ Kan 化した単体的局所化を適用する。
規約：対象は元の cofibrant 代数、Hom の宇宙は u+1。
使われ方：coherent nerve と写像空間の比較。 -/
abbrev CAlgSimplicialCategory := KanLocalizationCategory (cofibrantAlgebraRelativeCategory A)

/-- 概要：cofibrant E 代数の実際の coherent nerve としての CAlg_R（HTT 1.1.5）。
方針：同じ具体的な相対圏の Kan 化した単体的局所化へ nerve を適用する。
規約：任意の可換環上で追加のモデル構造・標数の入力仮定を付けない。
使われ方：E2b の E∞ 代数の ∞ 圏の構成。 -/
def CAlg_R : SSet.{u + 1} :=
  localizationNerve (cofibrantAlgebraRelativeCategory A)

/-- 概要：具体的な CAlg_R は quasicategory（HTT 1.1.5.10）。
方針：元の全 Hom の Kan 性から構成した一般の nerve の定理を使う。
規約：quasicategory 性の入力仮定は不要。
使われ方：CAlg_R の ∞ 圏的な操作。 -/
instance cAlg_R_quasicategory : SSet.Quasicategory (CAlg_R A) :=
  localizationNerve_quasicategory _

/-- 概要：CAlg_R の Hom は元の自由局所化 Hom の同じ Ex∞（Dwyer–Kan）。
方針：cofibrant 相対圏への代入と豊穣構造の移送の定義を評価する。
規約：Hom を離散化しない。
使われ方：既存の Kan Map^h との高次の比較の対象。 -/
lemma cAlg_sHom (X Y : CAlgSimplicialCategory A) :
    SimplicialCategory.sHom X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj
      (localizationHom (cofibrantAlgebraRelativeCategory A) X Y) := rfl

/-- 概要：CAlg_R の構成に使うすべての Hom は Kan 複体（Dwyer–Kan）。
方針：同じ Ex∞ の Kan 性を具体的な相対圏へ代入する。
規約：元の代数や単体集合のモデル構造の入力仮定を加えない。
使われ方：CAlg_R の写像空間比較の局所 Kan な入力。 -/
lemma cAlg_sHom_kanComplex (X Y : CAlgSimplicialCategory A) :
    SSet.KanComplex (SimplicialCategory.sHom X Y) := inferInstance

/-- 概要：CAlg_R の頂点は元の同じ cofibrant 代数の対象（HTT 1.1.5）。
方針：同じ coherent nerve の零単体の同値を代入する。
規約：対象の同型類への商を取らない。
使われ方：元の代数の頂点の供給。 -/
def cAlgVertexEquiv : CAlgSimplicialCategory A ≃ (CAlg_R A) _⦋0⦌ :=
  localizationNerveVertexEquiv _

/-- 概要：任意の元の E 代数から CAlg_R の頂点を作る（Dwyer–Kan）。
方針：同じ具体的な cofibrant 置換の対象を coherent nerve の頂点へ送る。
規約：元の代数に cofibrancy を仮定しない。
使われ方：元の全代数からの ∞ 関手の対象部分。 -/
def cAlgVertex (X : (operad A).Algebra) : (CAlg_R A) _⦋0⦌ :=
  cAlgVertexEquiv A ((cofibrantAlgebraDKReplacement A).obj X)

/-- 概要：通常の可換代数から CAlg_R の頂点を作る（BF §1、HTT 1.1.5）。
方針：元の離散 E 代数の同じ cofibrant 置換を頂点へ送る。
規約：頂点の構成であり、∞ 関手と離散性の比較は後続で証明する。
使われ方：E2b の離散対象の対象部分。 -/
def discreteCAlgVertex (B : CommAlgCat.{u} A) : (CAlg_R A) _⦋0⦌ :=
  cAlgVertex A ((discreteAlgebraFunctor A).obj B)

end SerrePositivity.EInfinity.BarrattEccles
