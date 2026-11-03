module

public import SerrePositivity.EInfinity.BarrattEccles.ExtraDegeneracy
public import SerrePositivity.EInfinity.BarrattEccles.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# Barratt–Eccles 正規化鎖の収縮

概要：Berger–Fresse §1.1 の EΣₙ の正規化鎖と次数 0 の A との鎖ホモトピー同値を構成する。
方針：追加退化の線形化による交代面鎖複体の収縮を、正規化 Moore 複体へ移す。
規約：このファイルの同値は自然数次数の鎖複体で述べる。
使われ方：E(n) の augmentation の擬同型性の入力となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：一点上の自由 A 加群は A 自身と同型である（Berger–Fresse §1.1）。
方針：一点集合の同値と自由加群関手のモノイダル単位の同型を使う。
規約：入力の一点集合は小さい PUnit の宇宙持ち上げ。
使われ方：正規化鎖の augmentation の値を A と同定する。 -/
def singletonFreeIso : (ModuleCat.free A).obj (ULift.{u} PUnit.{1}) ≅ 𝟙_ (ModuleCat A) :=
  (ModuleCat.free A).mapIso
    (Equiv.toIso (Equiv.ofUnique (ULift.{u} PUnit.{1}) PUnit.{u + 1})) ≪≫
    (ModuleCat.FreeMonoidal.εIso A).symm

/-- 概要：EΣₙ の正規化鎖は次数 0 の A と鎖ホモトピー同値である（Berger–Fresse §1.1）。
方針：Moore 複体と交代面鎖複体の同値、追加退化の収縮、一点自由加群の同型を合成する。
規約：基礎環の標数を制限せず、群同変な収縮は主張しない。
使われ方：Barratt–Eccles 複体の各 arity の augmentation の擬同型性を与える。 -/
def normalizedChainContraction (n : ℕ) :
    HomotopyEquiv
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((linearization A).obj (simplicial n)))
      ((ChainComplex.single₀ (ModuleCat A)).obj (𝟙_ (ModuleCat A))) :=
  AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex.trans
    (((extraDegeneracy n).map (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)).homotopyEquiv.trans
      (HomotopyEquiv.ofIso ((ChainComplex.single₀ (ModuleCat A)).mapIso (singletonFreeIso A))))

/-- 概要：E(n) は次数 0 の A とコチェインの鎖ホモトピー同値である（Berger–Fresse §1.1）。
方針：正規化鎖の収縮とホモトピーを q ↦ −q に沿って延長し、一点複体の延長を同定する。
規約：可縮性は augmentation を持つ分解として述べ、E(n) 自身が零とは主張しない。
使われ方：各 arity の E(n) → Com(n) の弱同値性を支える。 -/
def complexContraction (n : ℕ) : HomotopyEquiv (complex A n) (complexSphere A 0) := by
  let h := normalizedChainContraction A n
  let e := ComplexShape.embeddingDownNat
  let h' : HomotopyEquiv
      (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((linearization A).obj (simplicial n))).extend e)
      (((ChainComplex.single₀ (ModuleCat A)).obj (𝟙_ (ModuleCat A))).extend e) := {
    hom := HomologicalComplex.extendMap h.hom e
    inv := HomologicalComplex.extendMap h.inv e
    homotopyHomInvId := by
      simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id]
        using h.homotopyHomInvId.extend e
    homotopyInvHomId := by
      simpa only [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id]
        using h.homotopyInvHomId.extend e }
  exact h'.trans (HomotopyEquiv.ofIso
    (HomologicalComplex.extendSingleIso e (𝟙_ (ModuleCat A)) 0 0 rfl))

/-- 概要：Barratt–Eccles 複体の A への augmentation（Berger–Fresse §1.1）。
方針：一点への単体 augmentation から構成した収縮の順方向の射を取る。
規約：値は次数 0 に集中した A のコチェイン複体。
使われ方：可換オペラッドへの射の arity 成分となる。 -/
def complexAugmentation (n : ℕ) : complex A n ⟶ complexSphere A 0 :=
  (complexContraction A n).hom

/-- 概要：各 arity の augmentation は擬同型である（Berger–Fresse §1.1）。
方針：構成した鎖ホモトピー同値の順方向の射はホモロジー同型を誘導する。
規約：標数を制限しない任意の可換基礎環について成立する。
使われ方：E → Com の arity ごとの弱同値性を与える。 -/
lemma complexAugmentation_quasiIso (n : ℕ) :
    QuasiIso (complexAugmentation A n) :=
  HomotopyEquiv.quasiIso_hom (complexContraction A n)

end SerrePositivity.EInfinity.BarrattEccles
