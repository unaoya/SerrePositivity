module

public import SerrePositivity.EInfinity.BarrattEccles.Degrees
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# 正規化複体と非退化単体の自由加群

概要：Berger–Fresse §1.1 の E(n) の各鎖次数を非退化置換列上の自由加群と同定する。
方針：単体集合の標準 splitting を線形化し、非退化鎖複体と正規化 Moore 複体の同型を使う。
規約：非退化単体の添字集合の宇宙を A に合わせて持ち上げる。
使われ方：E(n) の自由基底と Σ-cofibrancy の証明に用いる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory CategoryTheory.Idempotents
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：EΣₙ の自由単体加群の標準 splitting（Berger–Fresse §1.1）。
方針：非退化単体による splitting を自由加群関手で送る。
規約：次数 q の非退化部分はその非退化単体上の自由 A 加群。
使われ方：正規化複体の自由加群表示を構成する。 -/
def linearSplitting (n : ℕ) : ((linearization A).obj (simplicial n)).Splitting := by
  letI := (ModuleCat.adj A).isLeftAdjoint
  exact (simplicial n).splitting.map (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)

/-- 概要：非退化単体の鎖複体と正規化 Moore 複体の同型（Berger–Fresse §1.1）。
方針：両複体の Karoubi 包絡での標準同型を忠実充満な包含に沿って戻す。
規約：次数は自然数の鎖次数である。
使われ方：各次数の基底を Moore 複体へ移す。 -/
def nondegenerateChainIso (n : ℕ) :
    (linearSplitting A n).nondegComplex ≅
      (AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((linearization A).obj (simplicial n)) :=
  (toKaroubi _).preimageIso
    ((linearSplitting A n).toKaroubiNondegComplexIsoN₁ ≪≫
      (AlgebraicTopology.DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi
        (ModuleCat A)).app _)

/-- 概要：E(n) の各非正次数の成分は非退化置換列上の自由加群である（Berger–Fresse §1.1）。
方針：次数の移送同型と非退化鎖複体の同型を合成する。
規約：q 鎖はコチェイン次数 −q に置く。
使われ方：群作用と可縮性を具体的な基底で計算する。 -/
def complexFreeIso (n q : ℕ) :
    (complex A n).X (-(q : ℤ)) ≅
      (ModuleCat.free A).obj (ULift.{u} ((simplicial n).nonDegenerate q)) :=
  complexXIso A n q ≪≫
    (HomologicalComplex.eval _ _ q).mapIso (nondegenerateChainIso A n).symm

/-- 概要：非退化置換列で添字づけられた E(n) の基底（Berger–Fresse §1.1）。
方針：有限台関数の標準基底を正規化複体との線形同値で移送する。
規約：コチェイン次数 −q の基底であり、基礎環の標数を制限しない。
使われ方：Σₙ の作用を基底の置換として記述する。 -/
def complexBasis (n q : ℕ) :
    Module.Basis (ULift.{u} ((simplicial n).nonDegenerate q)) A
      ((complex A n).X (-(q : ℤ))) :=
  (Finsupp.basisSingleOne : Module.Basis _ A
    (ULift.{u} ((simplicial n).nonDegenerate q) →₀ A)).map
      (complexFreeIso A n q).toLinearEquiv.symm

end SerrePositivity.EInfinity.BarrattEccles
