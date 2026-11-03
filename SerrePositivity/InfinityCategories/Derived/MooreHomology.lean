module
public import SerrePositivity.InfinityCategories.Derived.MooreComplex
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-! # Moore ホモロジーと負次数 Hom コホモロジー

概要：右写像空間の Moore ホモロジーは全非負次数で H^{-n} Hom と同型である。
方針：Moore 複体の同型、宇宙持ち上げの完全性、smart truncation の擬同型を使う。
規約：次数零も含む。使われ方：ホモトピー群と Ext の比較の中間段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison AlgebraicTopology
variable {S : Type u} [CommRing S] {D : Type v} [DGCategory S D]

/-- 概要：非正切断 Hom の chain ホモロジーは元の Hom の負次数コホモロジーである。
方針：shape の延長のホモロジー同型と切断からの擬同型を合成する。
規約：n=0 を含み、零項は cycles のまま使う。使われ方：Moore ホモロジーの計算。 -/
def connectiveHomHomologyIso (x y : D) (n : ℕ) :
    (connectiveHomComplex (R := S) x y).homology n ≅
      (homObject S D x y).homology (-(n : ℤ)) := by
  let K := homObject S D x y
  let e := ComplexShape.embeddingUpIntLE 0
  have he : e.f n = -(n : ℤ) := by simp [e]
  have := HomologicalComplex.quasiIsoAt_ιTruncLE K e he
  exact ((K.truncLE' e).extendHomologyIso e he).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(n : ℤ))).mapIso (K.truncLEIso e).symm ≪≫
      isoOfQuasiIsoAt (HomologicalComplex.ιTruncLE K e) (-(n : ℤ))

/-- 概要：実際の pinched Moore 複体のホモロジーは H^{-n} Hom の宇宙持ち上げである。
方針：複体の同型をホモロジーに送り、完全な ULift のホモロジー交換を使う。
規約：加群の同型として全非負次数を扱う。使われ方：π と Ext の比較の線形部分。 -/
def pinchedHomMooreHomologyIso (x y : D) (n : ℕ) :
    (((normalizedMooreComplex (ModuleCat.{max u v} S)).obj
      (pinchedHomModule x y)).homology n) ≅
      (ModuleCat.uliftFunctor.{v} S).obj ((homObject S D x y).homology (-(n : ℤ))) := by
  let U := ModuleCat.uliftFunctor.{v} S
  let K := connectiveHomComplex (R := S) x y
  exact (HomologicalComplex.homologyFunctor _ _ n).mapIso (pinchedHomMooreIso x y) ≪≫
    (K.sc n).mapHomologyIso U ≪≫ U.mapIso (connectiveHomHomologyIso x y n)

end SerrePositivity.InfinityCategories
