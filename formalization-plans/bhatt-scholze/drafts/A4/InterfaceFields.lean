-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Construction.InterfaceFields（仮。E3 の CAlg 版界面の欄 perfd・unit・h0）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md §2.3、単位 A4-3。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationBaseChangeHom
-- 本ファイルは drafts/A4/Perfectoidization.lean、drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology,HodgeTateFiltration,BaseChangeAndTensor}.lean を import する。

/-!
# E3 の界面の欄 `perfd`・`unit`・`h0` の構成（BS 著者版 Def 8.2 を関手にしたもの）

## 概要
`TheoryPerfectoidizationInterface` の最初の三欄を、A4-1 の S_perfd から作る。`e3Perfd : algebraNerve R ⟶ CAlg_R R` は
S ↦ (S^∧)_perfd（S^∧ は界面の `completionRing`、導来 p 完備化の H⁰）、`e3Unit` は S → S^∧ = Fil_0 Δ̄_{S^∧} → Δ̄_{S^∧} → Δ̄_{S^∧,perf} = (S^∧)_perfd
の合成の coherent な単位、`e3H0RingData` は H⁰(S_perfd) の環の関手と加群構造・射・単位との整合。

## 方針
Def 8.2 は導来 p 完備な S にだけ定義されている（D41）ので、界面の欄は S^∧ = completionRing S = π_0(LΛ_p S) を経由して定める。直接の式
(colim_φ Δ_S)^∧ ⊗ A/d を非完備な離散 S に当てたものと一致することは二段（W9-II-03）：Δ_S ≃ Δ_{LΛ_p S}（A2-4 `derivedPrismaticCohomology_completion_animated`）と
(LΛ_p S)_perfd ≃ (π_0 LΛ_p S)_perfd（A5-1 `perfectoidization_piZero`、Prop 8.5 系 4）。
関手性は A2 の Δ（`derivedPrismaticCohomologyDiscrete`、nerve の射）から：Frobenius の塔・余極限・完備化・⊗ A/d をすべて関手の段で取る。

## 規約
欄の型は Interface.lean / EInfinity/Perfectoidization/Interface.lean の現行の型に合わせる（`FunctorHom`、`H0RingData`、`underlyingUnit`）。
2b の改名表が来たら名前を追従する（`completionRing` など）。

## 使われ方
`TheoryPerfectoidizationInterface` の構成（A9）。残りの欄 universal（A7 Cor 8.14）、limitCone・limit_isLimit（A5 Prop 8.5）、integral（A8 Thm 10.11）、
excision（A6 Cor 8.12）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-! ## 関手の段の Def 8.2 -/

/-- 概要：Def 8.2 (1) を関手として：algebraNerve R（離散 R 代数）→ CAlg_A、S ↦ Δ_{S/A,perf}。
方針：`derivedPrismaticCohomologyDiscrete`（A2-2、k = R = A/d）の Frobenius の塔（`frobeniusTower` の関手版）の CAlg_A での
sequential 余極限（G-A4-2、関手の圏で点ごと）と完備化の関手（G-A2-3）の合成。
規約：定義域は離散 R 代数全体（Δ は A2 で全 animated 代数に定義済み）。Def 8.2 の意味をもつのは導来 p 完備な S だけ（D41）。
使われ方：`perfectoidizationFunctor`。 -/
def prismaticPerfectionFunctor (hR : IsIntegralPerfectoid R p) : algebraNerve R ⟶ E.CAlg (perfectPrismRing p R) :=
  directPerfectionFunctor (E := E) p R hR

/-- 概要：Def 8.2 (2) を関手として：S ↦ Δ_perf ⊗^L_A A/d。
方針：`prismaticPerfectionFunctor` と底変換 CAlg_A → CAlg_R（G-A4-4、`perfectPrism_quotientEquiv` で A/d ≅ R）の合成。
規約：—
使われ方：`e3Perfd`。 -/
def perfectoidizationFunctor (hR : IsIntegralPerfectoid R p) : algebraNerve R ⟶ E.CAlg R :=
  prismaticPerfectionFunctor (E := E) p R hR ≫ modPrismFunctor (E := E) p R hR

/-- 概要：点ごとの値は A4-1 の `perfectoidization` に一致する。
方針：定義の展開（余極限・完備化・底変換は点ごと）。
規約：`VertexIso`（CAlg_R R の頂点の同型）。
使われ方：Lemma 8.4 を欄に移す。 -/
def perfectoidizationFunctor_vertex (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((perfectoidizationFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))) (perfectoidization (E := E) p R hR S hS) :=
  (directPerfectionVertex (E := E) p R hR (ofAlgebra R S)).map (modPrismFunctor (E := E) p R hR)

/-! ## 完備化の関手 -/

/-- 概要：S ↦ S^∧（`completionRing`、導来 p 完備化の H⁰）の A_R R 上の関手。
方針：`completionRing` の普遍性（Interface.lean の ∃! g, completionUnit ≫ g = f）で射を定め、関手性も普遍性から。
規約：R 代数の構造は `completionUnit` の合成。
使われ方：`e3Perfd`。本体の completionFunctor は射を完備化の普遍性で送る。 -/
def completionFunctor : A_R R ⥤ A_R R := PerfectoidizationInterface.completionFunctor p R

/-- 概要：単位 S → S^∧ の自然変換。
方針：`completionUnit`。
規約：—
使われ方：`e3Unit` の最初の段。 -/
def completionFunctorUnit : 𝟭 (A_R R) ⟶ completionFunctor p R := PerfectoidizationInterface.completionAlgebraUnit p R

/-! ## 欄 perfd -/

/-- 概要：E3 の `perfd`：S ↦ (S^∧)_perfd（D41、界面の規約）。
方針：`nerveMap (completionFunctor p R) ≫ perfectoidizationFunctor p R`。
規約：`algebraNerve R = nerve (A_R R)` は SSet.{u+1}。
使われ方：`TheoryPerfectoidizationInterface.perfd`。 -/
def e3Perfd (hR : IsIntegralPerfectoid R p := by assumption) : algebraNerve R ⟶ E.CAlg R :=
  nerveMap (completionFunctor p R) ≫ perfectoidizationFunctor (E := E) p R hR

/-- 通常の R 代数の同型を、その二本の射の nerve により頂点同型にする。 -/
def algebraNerveIso {U V : A_R R} (e : U ≅ V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex V) where
  hom := SSet.Truncated.HomotopyCategory.homMk (nerve.edgeMk e.hom).toTruncated
  inv := SSet.Truncated.HomotopyCategory.homMk (nerve.edgeMk e.inv).toTruncated
  hom_inv_id := by sorry -- nerve の合成三角形と e.hom_inv_id
  inv_hom_id := by sorry -- 同じく e.inv_hom_id

/-- 概要：導来 p 完備な S では `e3Perfd` の値は Def 8.2 の S_perfd そのもの（S^∧ ≅ S）。
方針：`completionUnit` が同型（`IsModuleComplete` のもとで H⁰ の完備化単位は同型）と `perfectoidizationFunctor_vertex`。
規約：`VertexIso`。
使われ方：Lemma 8.4 (c)・Cor 8.14 を欄に移す。 -/
def e3Perfd_of_complete (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((e3Perfd (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))) (perfectoidization (E := E) p R hR S hS) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    ((perfectoidizationFunctor (E := E) p R hR).app _
      ((nerveMap (completionFunctor p R)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))))
    (perfectoidization (E := E) p R hR S hS)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex, nerveMap_app_mk₀]
  exact (algebraNerveIso R (PerfectoidizationInterface.completionAlgebraUnitIso p R ⟨ofAlgebra R S, hS⟩).symm).map
    (perfectoidizationFunctor (E := E) p R hR) ≪≫ perfectoidizationFunctor_vertex (E := E) p R hR S hS

-- `e3Perfd_eq_direct`（直接の式との一致、Prop 8.5 系 4 を使う）は drafts/A4/AfterComparison.lean へ（W9-III-09：本ファイルは A5 より先）。

/-- 概要：D(R) 版の `perfd`（忘却 U との合成）。
方針：`e3Perfd ≫ cAlgForgetDerived R`。
規約：`nonempty_e3_of_theory` がこの形で D(R) 版を作るので、別に定義は要らない（記録のみ）。
使われ方：—（`nonempty_e3_of_theory`）。 -/
abbrev e3PerfdDerived (hR : IsIntegralPerfectoid R p) : algebraNerve R ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R :=
  e3Perfd (E := E) p R hR ≫ E.forget R

theorem e3Perfd_derived (hR : IsIntegralPerfectoid R p) :
    e3PerfdDerived (E := E) p R hR = e3Perfd (E := E) p R hR ≫ E.forget R := rfl

/-! ## 欄 unit -/

def directHodgeTateFunctor (hR : IsIntegralPerfectoid R p) : algebraNerve R ⟶ E.CAlg R :=
  discreteDeltaFunctor (E := E) p R hR ≫ modPrismFunctor (E := E) p R hR

/-- S→LΛ_p S≃Fil₀→Δ̄_S の自然変換。完備入力では最初の単位が同値。 -/
def directHodgeTateUnit (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) (directHodgeTateFunctor (E := E) p R hR) := by
  sorry -- A2 待ち：hodgeTateUnitCAlg の離散入力への制限。BS-D4 で Fil₀ の CAlg 自然変換に接続

def directToPerfection (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (directHodgeTateFunctor (E := E) p R hR) (perfectoidizationFunctor (E := E) p R hR) :=
  Classical.choose (show ∃ η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (directHodgeTateFunctor (E := E) p R hR) (perfectoidizationFunctor (E := E) p R hR),
    ∀ U : A_R R, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U) = (hoFunctor.map (modPrismFunctor (E := E) p R hR)).toFunctor.map
      (directPerfectionLeg (E := E) p R hR U ≫ (directPerfectionVertex (E := E) p R hR U).inv) from by
    sorry) -- 第0脚と完備化単位の自然変換を A/d に底変換する

/-- 概要：S^∧ → Δ̄_{S^∧} = Δ_{S^∧} ⊗^L_A A/d の自然変換（Fil_0 Δ̄ = S^∧、A2-3 の `hodgeTateFiltration_zero`）。
方針：`algebraEmbedding R ≫ (⋯)` から `derivedPrismaticCohomologyDiscrete ≫ 底変換` への `FunctorHom`。HT filtration の Fil_0 → 全体の
自然変換（Kan 延長の自然変換）に、Fil_0 ≅ 完備化の同型を前置する。
規約：`FunctorHom`（CAlg_R R の関手の圏の射）。
使われ方：`e3Unit` の第二段。 -/
def hodgeTateUnit (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap (completionFunctor p R) ≫ E.discrete R)
      (nerveMap (completionFunctor p R) ≫ directHodgeTateFunctor (E := E) p R hR) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom _ (directHodgeTateUnit (E := E) p R hR)

/-- 概要：Δ̄_S → Δ̄_{S,perf} = S_perfd の自然変換（Frobenius の余極限の 0 番目の脚の mod d、完備化の単位との合成）。
方針：余極限の脚（関手の圏で点ごと）と完備化の単位（G-A2-3 の反射の単位）の合成、底変換で ⊗ A/d。
規約：—
使われ方：`e3Unit` の第三段。 -/
def toPerfection (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (nerveMap (completionFunctor p R) ≫ directHodgeTateFunctor (E := E) p R hR) (e3Perfd (E := E) p R hR) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom _ (directToPerfection (E := E) p R hR)

/-- BS 著者版 Def 8.2 の完備化単位の成分。同じ nerve の辺の始域・終域だけを揃える。 -/
def completionUnitCAlgComponent (U : A_R R) :
    HomotopyCategory.mk ((E.discrete R).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) ⟶
      HomotopyCategory.mk ((nerveMap (completionFunctor p R) ≫ E.discrete R).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) := by
  change HomotopyCategory.mk ((E.discrete R).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) ⟶
    HomotopyCategory.mk ((E.discrete R).app (Opposite.op ⦋0⦌)
      ((nerveMap (completionFunctor p R)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex, nerveMap_app_mk₀]
  convert SSet.Truncated.HomotopyCategory.homMk
    (((nerve.edgeMk ((completionFunctorUnit p R).app U)).map (E.discrete R)).toTruncated) using 1 <;> rfl

def completionToCAlgUnit :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) (nerveMap (completionFunctor p R) ≫ E.discrete R) :=
  Classical.choose (show ∃ η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R)
      (nerveMap (completionFunctor p R) ≫ E.discrete R),
    ∀ U : A_R R, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U) =
      completionUnitCAlgComponent (E := E) p R U from by
    sorry) -- 完備化単位の自然性を nerve と離散 CAlg 埋め込みで送る

/-- 概要：E3 の `unit`：S → S^∧ → Δ̄_{S^∧} → (S^∧)_perfd の coherent な単位。
方針：`nerveMap completionFunctorUnit`（離散の段、`algebraEmbedding` を通す）、`hodgeTateUnit`、`toPerfection` の合成。
各段が関手の圏の射なので合成も射。
規約：`FunctorHom (algebraEmbedding R) (e3Perfd p R)`。
使われ方：`TheoryPerfectoidizationInterface.unit`。 -/
def e3Unit (hR : IsIntegralPerfectoid R p := by assumption) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (E.discrete R) (e3Perfd (E := E) p R hR) :=
  completionToCAlgUnit (E := E) p R ≫ hodgeTateUnit (E := E) p R hR ≫ toPerfection (E := E) p R hR

/-- 概要：導来 p 完備な S では、`e3Unit` の S 成分は Def 8.2 の S → S_perfd（Fil_0 → 余極限の脚）に `e3Perfd_of_complete` を通して一致する。
方針：定義の展開。
規約：—
使われ方：Cor 8.14（universal の欄）の証明で単位を原典の射に読み替える。 -/
theorem e3Unit_of_complete (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S)
    let e := e3Perfd_of_complete (E := E) p R hR S hS
    let v := perfectoidizationFunctor_vertex (E := E) p R hR S hS
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (e3Unit (E := E) p R hR) s ≫ e.hom =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (directHodgeTateUnit (E := E) p R hR ≫ directToPerfection (E := E) p R hR) s ≫ v.hom := by
  sorry -- 完備化単位が同型のとき、その自然性で二つの単位を同じ S_perfd 上で比較

/-! ## 欄 h0 -/

/-- 概要：H⁰((S^∧)_perfd) の通常の R 代数の関手 A_R R ⥤ A_R R。
方針：界面の π₀ から可換環とその射を読み、pi0_forget で H⁰ と比較する。
R 代数の構造は `e3Unit` の H⁰。
規約：`H0RingData.ringFunctor`。
使われ方：`e3H0RingData`。 -/
def e3H0RingFunctor (hR : IsIntegralPerfectoid R p) : A_R R ⥤ A_R R where
  obj S := cAlgH0Algebra (E := E) R ((e3Perfd (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S))
  map f := (cAlgH0OnHomotopy (E := E) R).map (SSet.Truncated.HomotopyCategory.homMk
    (((nerve.edgeMk f).map (e3Perfd (E := E) p R hR)).toTruncated))
  map_id := by sorry -- H⁰ の恒等射
  map_comp := by sorry -- nerve の合成三角形を H⁰ で読む

/-- 離散代数の H⁰ は元の通常の代数であるという標準比較。 -/
def discreteToH0 (U : A_R R) : U ≅ cAlgH0Algebra (E := E) R ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) := by
  sorry -- 離散代数の cofibrant 置換の擬同型は H⁰ 上で代数同型を誘導する

/-- 概要：E3 の `h0`：環の関手、加群構造との同型（`moduleIso`）、射との整合（`map_compat`）、環の単位（`unit`）、単位との整合（`unit_compat`）。
方針：`moduleIso` は「CAlg の H⁰ の底の加群 = D(R) の H⁰」（U と H⁰ の可換性）、`map_compat` は H⁰ の関手性、`unit` は `e3Unit` の H⁰、
`unit_compat` は `underlyingUnit` の構成（`functorHomHomotopy`）と H⁰ の可換性。
規約：`H0RingData R (e3Perfd ≫ cAlgForgetDerived R) (underlyingUnit R e3Unit)`。
使われ方：`TheoryPerfectoidizationInterface.h0`。 -/
def e3H0RingData (hR : IsIntegralPerfectoid R p := by assumption) :
    H0RingData R (e3PerfdDerived (E := E) p R hR) (theoryUnderlyingUnit (E := E) R (e3Unit (E := E) p R hR)) where
  ringFunctor := e3H0RingFunctor (E := E) p R hR
  moduleIso := by sorry -- H⁰ の乗法を忘れた加群と underlying derived vertex の H⁰ の標準比較
  map_compat := by sorry -- 同じ辺を H⁰ と U で送った自然性
  unit := {
    app := fun S => (discreteToH0 (E := E) R S).hom ≫
      (cAlgH0OnHomotopy (E := E) R).map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (e3Unit (E := E) p R hR) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S))
    naturality := by sorry } -- e3Unit の自然性を H⁰ に移す
  unit_compat := by sorry -- underlyingUnit の指定成分と HMap が上の環準同型を与える

/-- 概要：導来 p 完備な S では H⁰((S^∧)_perfd) = H⁰(S_perfd)、かつ S_perfd ∈ D^{≥0}（Lemma 8.4 (c)）なので
H⁰ は S_perfd の「最初の」コホモロジー。離散なら S_perfd 自身。
方針：`e3Perfd_of_complete`、`perfectoidization_coconnective`。
規約：—
使われ方：Cor 8.14（universal）、integral の欄（A8）。 -/
theorem e3H0_of_complete (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let U := ofAlgebra R S
    Nonempty (((e3H0RingData (E := E) p R hR).ringFunctor.obj U) ≅ cAlgH0Algebra (E := E) R (perfectoidization (E := E) p R hR S hS)) ∧
      InfinityCategories.Derived.IsCoconnectiveAt R 0 (vertex R (e3PerfdDerived (E := E) p R hR) U) := by
  sorry -- e3Perfd_of_complete の同型を cAlgH0OnHomotopy で送り、Lemma 8.4(c) を U で移送

end SerrePositivity.BhattScholze.Perfectoidization.Derived
