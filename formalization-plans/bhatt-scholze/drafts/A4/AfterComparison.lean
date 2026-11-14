-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Construction.AfterComparison（仮。Prop 8.5 の後に置く A4 の補足：D41 の直接の式との一致、Example 8.3）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md §2.1 D41・Ex 8.3、単位 A4-3・A4-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
-- 本ファイルは drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A5/PerfectSiteComparison.lean（Prop 8.5 系 4 `perfectoidization_piZero`）、
-- drafts/A2/BaseChangeAndTensor.lean を import する（W9-III-09：A4 の定義は A5 より先、本ファイルは A5 より後）。

/-!
# Prop 8.5 の後に置く A4 の補足（D41 の直接の式との一致、BS 著者版 Example 8.3）

## 概要
`e3Perfd_eq_direct`：任意の離散 S で E3 の `perfd` の値（(completionRing S)_perfd、D41）が直接の式 (colim_φ Δ_S)^∧ ⊗^L_A A/d に一致する
（Prop 8.5 系 4）。`perfectoidization_charP`：標数 p では S_perfd は通常の完全化の p 完備化（Prop 8.5 で A によらないことを使う）。

## 方針
W9-III-09 で A4/InterfaceFields.lean・A4/Perfectoidization.lean から切り出した。どちらも Prop 8.5 を使うので A4 の定義（A5 より先）と同居できない。

## 規約
所有単位は A4 のまま。

## 使われ方
A6（Prop 8.10：任意の離散 S に対する arc 層としての記述）、A8。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-- 概要：任意の離散 S で、`e3Perfd` の値は直接の式 (colim_φ Δ_S)^∧ ⊗^L_A A/d（S を完備化せずに A2 の Δ_S に当てたもの）に一致する。
方針：D32 の animated 版（Δ_S ≃ Δ_{LΛ_p S}、A2-4 `derivedPrismaticCohomology_completion_animated`）で直接の式は (LΛ_p S)_perfd、
Prop 8.5 の系 4（A5-1 `perfectoidization_piZero`）で (LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd = (completionRing S)_perfd（W9-I-29、決定 6）。
規約：これが D41 の「直接の式との一致は定理」。
使われ方：A6（Prop 8.10：任意の離散 S に対する arc 層としての記述）、A8。 -/
theorem e3Perfd_eq_direct (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S] :
    let U := ofAlgebra R S
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((e3Perfd (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))
      ((modPrismFunctor (E := E) p R hR).app _ (directPerfectionValue (E := E) p R hR U))) := by
  sorry -- D32 で LΛ_p S へ、Prop 8.5 系4で π₀ LΛ_p S へ移す。完備化 H⁰ と導来完備化を区別

/-! ## Example 8.3（標数 p） -/

/-- char p の通常環の完全化は Frobenius に沿う順方向の余極限。p=0 を使い零環も含める。 -/
def ordinaryFrobeniusDiagram (S : Type u) [CommRing S] (hpS : (p : S) = 0) : ℕ ⥤ CommRingCat.{u} := by
  let F : S →+* S := {
    toFun := fun s => s ^ p
    map_one' := one_pow _
    map_mul' := fun x y => mul_pow x y p
    map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
    map_add' := by sorry } -- p が素数で p = 0 なので二項係数の中間項が消える
  exact Functor.ofSequence (X := fun _ => CommRingCat.of S) (fun _ => CommRingCat.ofHom F)

/-- 完全化の第0脚と p 完備化単位を合成して R 代数として読む。 -/
def completedCharPPerfection (S : Type u) [CommRing S] [Algebra R S] (hpS : (p : S) = 0) : A_R R :=
  let D := ordinaryFrobeniusDiagram p S hpS
  Under.mk (CommRingCat.ofHom (algebraMap R S) ≫ colimit.ι D 0 ≫ completionUnit p (colimit D))

/-- 概要：Example 8.3：R が標数 p（A = W(R)、d = p）なら S_perfd ≅ (colim_φ S)^∧_p（通常の完全化の p 完備化）。
方針：A によらないこと（Prop 8.5、A5）で A = Z_p に帰着し、HT 比較の Frobenius 同変な S → Δ_S/p が完全化で同型（∧^i L_{S/F_p}[−i] 上の Frobenius は i ≠ 0 で零）。
規約：主張のみ。証明は A5 の後。A6（Prop 8.10 の tilt）で要るか確認。
使われ方：A6。 -/
theorem perfectoidization_charP (hR : IsIntegralPerfectoid R p) (hpR : (p : R) = 0)
    (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let hpS : (p : S) = 0 := by simpa using congrArg (algebraMap R S) hpR
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (perfectoidization (E := E) p R hR S hS)
      ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (completedCharPPerfection p R S hpS)))) := by
  sorry -- Prop 8.5 の基底独立性と HT 比較。正次数の graded piece 上で Frobenius は零

end SerrePositivity.BhattScholze.Perfectoidization.Derived
