-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Construction.DiscreteCore（仮。原典 Cor 8.14 前半の芯）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.3・§5（配置、W9-II-24）、単位 A7-2。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
-- 本ファイルは drafts/A4/Perfectoidization.lean、drafts/DerivedGeneral/Truncation.lean だけを import する（**A4/Perfectoidization の後、A5 より先**に置く。W9-III-14）。

/-!
# 芯 G-A7-5：S_perfd が離散なら perfectoid（BS 著者版 Cor 8.14 前半）

## 概要
S_perfd 離散 ⇒ Δ_{S/A,perf} 離散（d 進 Nakayama）⇒ 完全 p 完備 δ 環（A4 Lemma 8.4 (b)）⇒ 完全 prism（A4）⇒ S_perfd = Δ_perf/d は perfectoid 環（Thm 3.10）。

## 方針
W9-II-24 で A7/UniversalProperty.lean から切り出した。A5-2（semiperfectoid の場合：連結性を前置してここへ渡す）と A7-2（Cor 8.14）が共有するので、
入力を A4・導来 Nakayama・完全 prism の商だけに限り、Prop 8.5・Cor 8.14 後半に依存しない独立ファイルにする。所有単位は A7-2 のまま。

## 規約
S は導来 p 完備な R 代数（離散版。animated 版は `perfectoidizationAnimated` の制限で同じ主張）。`IsTheoryDiscrete`（EInfinity/Perfectoidization/TheoryInterface）。

## 使われ方
A5-2 `perfectoidization_discrete_of_semiperfectoid`・`perfectoidization_isIntegralPerfectoid_of_semiperfectoid`、A7-2 `perfectoidization_isPerfectoidization_of_discrete`。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))

/-! ## G-A7-5：芯（A5-2 と共有） -/

/-- 概要：S_perfd が離散なら Δ_{S/A,perf} も離散（d 進 Nakayama：d 完備で mod d が離散）。
方針：DerivedGeneral/Truncation。
規約：`IsTheoryDiscrete`。
使われ方：芯。 -/
theorem prismaticPerfection_discrete_of_perfectoidization_discrete (h : IsTheoryDiscrete (E := E) R (perfectoidization (E := E) p R hR S hS)) :
    IsTheoryDiscrete (E := E) (perfectPrismRing p R) (prismaticPerfection (E := E) p R hR S hS) := by
  sorry -- d 完備性と mod d の離散性に導来 Nakayama を適用する

/-- 概要：S_perfd 離散 ⇒ (H⁰(Δ_perf), (d)) は完全 prism（A4 `prismaticPerfection_h0_perfectDelta`・`prismaticPerfectionPrism`）。
方針：上と A4。
規約：`OrientedPrism`。
使われ方：perfectoid 性。 -/
theorem perfectoidization_perfectPrism_of_discrete (h : IsTheoryDiscrete (E := E) R (perfectoidization (E := E) p R hR S hS)) :
    let C := cAlgH0Algebra (E := E) (perfectPrismRing p R) (prismaticPerfection (E := E) p R hR S hS)
    let B := cAlgH0Algebra (E := E) R (perfectoidization (E := E) p R hR S hS)
    ∃ Q : OrientedPrism p C.right, Q.generator = C.hom.hom (perfectPrism p R hR).generator ∧
      Q.deltaStructure.IsPerfect ∧ Nonempty ((C.right ⧸ Q.ideal) ≃+* B.right) := by
  have hΔ := prismaticPerfection_discrete_of_perfectoidization_discrete (E := E) p R hR S hS h
  have hδ := prismaticPerfection_h0_perfectDelta (E := E) p R hR S hS
  let Q := prismaticPerfectionPrism (E := E) p R hR S hS
  sorry -- A4 の H⁰ の完全 δ 構造。両対象が離散で d が正則なので mod d の H⁰ は指定された商

/-- 概要：Cor 8.14 前半：S_perfd 離散 ⇒ S_perfd（環として H⁰）は perfectoid（完全 prism の商、`quotient_isIntegralPerfectoid`）。
方針：上。A5-2 の `perfectoidization_isIntegralPerfectoid_of_semiperfectoid` はこれに連結性を前置したもの。
規約：`IsIntegralPerfectoid (H⁰) p`。
使われ方：`universal` の第一成分。 -/
theorem perfectoidization_isIntegralPerfectoid_of_discrete (h : IsTheoryDiscrete (E := E) R (perfectoidization (E := E) p R hR S hS)) :
    IsIntegralPerfectoid (cAlgH0Algebra (E := E) R (perfectoidization (E := E) p R hR S hS)).right p := by
  sorry -- 上で同定した完全 prism の商に quotient_isIntegralPerfectoid を適用して移送する

end SerrePositivity.BhattScholze.Perfectoidization.Derived
