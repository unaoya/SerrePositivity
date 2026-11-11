module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# m 次ホモトピーからの複体ホモロジー写像の比較

概要：両端条件が次数 ≤m だけで成立するときも、その範囲の複体ホモロジー写像は一致する。
方針：区間から得られる実両端間の全鎖ホモトピーと、ホモロジー写像の当該次数の成分への依存性を使う。
規約：KST Definition A.3、Lemma A.4 の複体側の基礎。H_* 関手自体は定義しない。
使われ方：同変 bar への移送前の、m 次比較の正当化。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory HomologicalComplex
open scoped Simplicial

/-- 概要：同じ次数の成分が一致する二つの鎖写像は、その次数のホモロジー写像で一致する。
方針：サイクルの包含の単射性とホモロジーへの全射性で相殺する。
規約：KST Lemma A.4 の一般複体補題。使われ方：m 次の両端等式の移送。 -/
lemma homologyMap_eq_of_component_eq
    {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (f g : K ⟶ L) (n : ι) (h : f.f n = g.f n) :
    homologyMap f n = homologyMap g n := by
  have hc : cyclesMap f n = cyclesMap g n := by
    apply (cancel_mono (L.iCycles n)).mp
    rw [cyclesMap_i, cyclesMap_i, h]
  apply (cancel_epi (K.homologyπ n)).mp
  rw [homologyπ_naturality, homologyπ_naturality, hc]

/-- 概要：幾何的な区間包含の間の標準ホモトピー。
方針：区間上の恒等写像をホモトピーの写像とする。
規約：KST Definition A.3 の区間。使われ方：任意の線形区間写像の両端の比較。 -/
def geometricCylinderHomotopy (X : SSet.{u}) : SSet.Homotopy
    (SSet.ι₀ (X := X)) (SSet.ι₁ (X := X)) where
  h := 𝟙 _
  h₀ := by simp
  h₁ := by simp
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：自由加群のテンソル区間包含の間の組合せ的ホモトピー。
方針：幾何的な標準ホモトピーの自由化をテンソル同型の逆で移す。
規約：KST Definition A.3。使われ方：m 次ホモトピーの実両端の鎖ホモトピー。 -/
def linearizedCylinderHomotopy (X : SSet.{u}) :
    SimplicialObject.Homotopy (linearizedEndpoint₀ X) (linearizedEndpoint₁ X) :=
  (linearizedSpaceHomotopy (geometricCylinderHomotopy X)).postcomp
    (linearizedTensorIso X _).inv

/-- 概要：m 次ホモトピーの区間写像の実両端は全鎖ホモトピック。
方針：区間包含のホモトピーを区間写像と合成し、交代面写像複体へ送る。
規約：KST Definition A.3。実両端と指定された f,g の一致は次数 ≤m のみ。
使われ方：Lemma A.4 の次数制限のあるホモロジー比較。 -/
def LinearizedMHomotopy.endpointChainHomotopy
    {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    {f g : linearizedSpace X ⟶ D} {m : ℕ} (H : LinearizedMHomotopy f g m) :
    Homotopy
      ((AlgebraicTopology.alternatingFaceMapComplex _).map (linearizedEndpoint₀ X ≫ H.h))
      ((AlgebraicTopology.alternatingFaceMapComplex _).map (linearizedEndpoint₁ X ≫ H.h)) :=
  ((linearizedCylinderHomotopy X).postcomp H.h).toChainHomotopy

/-- 概要：m 次ホモトピックな二つの射の複体ホモロジー写像は次数 ≤m で一致する。
方針：実両端の全鎖ホモトピーと当該次数の成分一致を合成する。
規約：KST Lemma A.4 の非同変な複体側。所有レーンの H_* との模型同定は別界面。
使われ方：同変 bar に持ち上げた後の低次数比較。 -/
theorem LinearizedMHomotopy.homologyMap_eq
    {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
    {f g : linearizedSpace X ⟶ D} {m : ℕ} (H : LinearizedMHomotopy f g m)
    (n : ℕ) (hn : n ≤ m) :
    homologyMap ((AlgebraicTopology.alternatingFaceMapComplex _).map f) n =
      homologyMap ((AlgebraicTopology.alternatingFaceMapComplex _).map g) n := by
  let F := AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{u} ℤ)
  calc
    homologyMap (F.map f) n = homologyMap (F.map (linearizedEndpoint₀ X ≫ H.h)) n :=
      (homologyMap_eq_of_component_eq _ _ n (H.h₀ n hn)).symm
    _ = homologyMap (F.map (linearizedEndpoint₁ X ≫ H.h)) n :=
      H.endpointChainHomotopy.homologyMap_eq n
    _ = homologyMap (F.map g) n := homologyMap_eq_of_component_eq _ _ n (H.h₁ n hn)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
