-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Derived.Cohomology（仮。原典 Construction 7.6）
-- 設計書：formalization-plans/bhatt-scholze/a2-design.md §2.2・§2.4 (1)、単位 A2-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareHom

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

-- 本ファイルは drafts/A2/AnimatedAlgebra.lean、drafts/A0/{PrismaticSite,CechAlexander}.lean、drafts/Sheaves/CAlgValued.lean、
-- drafts/Shared/CosimplicialEInfinity.lean、drafts/DerivedGeneral/{CompletionFunctor,ScalarRestriction}.lean を import する。

/-!
# 導来 prismatic コホモロジー（BS 著者版 Construction 7.6）

## 概要
向き付き有界 prism (A,(d))、k = A/d。多項式 k 代数 P に Δ_{P^∧/A}（A0 の Not 4.16 の CAlg 版）を対応させる関手 Δ_0 : N(Poly k) → 𝒱
（𝒱 = (p,d) 完備な E∞-A 代数の ∞ 圏）を、P_Σ(N(Poly k))（単体的可換 k 代数）へ sifted 余極限を保つように延長したものを
導来 prismatic コホモロジー R ↦ Δ_{R/A} とする（HTT 5.5.8.15）。φ_A 半線形な Frobenius も Poly 上の φ の延長。
(1) 多項式代数での値は元の Δ（充満忠実な包含に沿う Kan 延長の制限）。

## 方針
A0 の `prismaticCohomology`（D(A) 値）を Sheaves/CAlgValued の `derivedGlobalSectionsCAlg` で CAlg 値にし、Čech–Alexander 模型の
Tot_{E∞}（Shared/CosimplicialEInfinity）と一致させる。延長は A2-1 の `exists_siftedExtension`。値の (p,d) 完備化は
DerivedGeneral/CompletionFunctor の反射（CAlg 版は要確認）。

## 規約
値は CAlg_A を正（a2-design §6 の 1）。D(A) 値は忘却 U で。始域は P_Σ 全体（D32）。離散 R の Δ_R は `discreteToAnimated` で。

## 使われ方
A2-3（HT filtration）、A2-4、A3（Lemma 7.7：Δ_R 離散なら δ 環）、A4（Def 8.2：Frobenius 余極限）、A5・A7・A8、E3 の `perfd`。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.DerivedCompletion
open SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface
attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)

/-! ## 値の圏 -/

/-- 概要：𝒱 := (p,d) 導来完備な E∞-A 代数の充満部分 ∞ 圏（CAlg_A の中）。
方針：DerivedGeneral/CompletionFunctor の `IsDerivedComplete` を U で引き戻した充満部分複体。
規約：sifted 余極限は CAlg_A で取って完備化（反射）。
使われ方：Δ の値。 -/
def completeAt (a : A) (x : (derivedInfinityCategory A) _⦋0⦌) : Prop :=
  IsComplete A a ((derivedInfinityHomotopyEquivalence A).functor.obj ⟨x⟩)

def prismComplete (x : (E.CAlg A) _⦋0⦌) : Prop :=
  let M := (E.forget A).app _ x
  completeAt (p : A) M ∧ completeAt P.generator M

abbrev CompleteCAlg : SSet.{u+1} := fullSubcomplexOnVertices (E.CAlg A) (prismComplete (E := E) P)
instance : Quasicategory (CompleteCAlg (E := E) P) := fullSubcomplexOnVertices_quasicategory _ _

def prismCompleteInclusion : CompleteCAlg (E := E) P ⟶ E.CAlg A := (fullSubcomplexOnVertices _ (prismComplete (E := E) P)).ι

def prismCompleteReflection : Σ L : E.CAlg A ⟶ CompleteCAlg (E := E) P, QCatAdjunction L (prismCompleteInclusion (E := E) P) := by
  sorry -- 要確認：G-A2-3・9。対称モノイダルな導来完備化の CAlg への反射

abbrev prismCompletion := (prismCompleteReflection (E := E) P).1
def prismCompletionUnit := (prismCompleteReflection (E := E) P).2.unitHom

abbrev prismModIdeal := cAlgBaseChange (E := E) (Ideal.Quotient.mk P.ideal)

/-- 概要：𝒱 は sifted 余極限をもつ（CAlg_A の sifted 余極限の完備化）。
方針：G-A2-3（完備化は反射）、G-A2-4（CAlg_A の sifted 余極限、HA 3.2.3.1）。
規約：—
使われ方：HTT 5.5.8.15 の仮定。 -/
theorem completeCAlg_siftedColimits : HasSmallSiftedColimits (CompleteCAlg (E := E) P) := by
  sorry -- CAlg_A の小 sifted 余極限を反射し、随伴で完備代数への余錐を判定する

/-! ## 多項式代数上の Δ_0（CAlg 値） -/

instance polySiteSmall (n : ℕ) : EssentiallySmall.{u} (PrismOver P (polyCompletion P n) (polyCutoff P n)) :=
  PrismOver.essentiallySmall (P := P) (R := polyCompletion P n) (by
    sorry) -- cutoff は #A+#R 以上

def testSiteRings (S : Type u) [CommRing S] [Algebra (A ⧸ P.ideal) S] (κ : Cardinal.{u})
    [EssentiallySmall.{u} (PrismOver P S κ)] : (PrismaticSite P S κ)ᵒᵖ ⥤ A_R A :=
  unopUnop _ ⋙ (equivSmallModel _).inverse ⋙ prismSiteAlgebras P S κ

def polyStructureRing (n : ℕ) : (PrismaticSite P (polyCompletion P n) (polyCutoff P n))ᵒᵖ ⥤ A_R A :=
  testSiteRings P (polyCompletion P n) (polyCutoff P n)

theorem polyStructureRing_forget (n : ℕ) :
    polyStructureRing P n ⋙ Under.forget (CommRingCat.of A) =
      unopUnop _ ⋙ structurePresheaf (E := E) P (polyCompletion P n) (polyCutoff P n) := by
  sorry -- 両辺は A0 の B と同じ環射を取る

abbrev polyStructure (n : ℕ) := Sheaves.ringPresheafToCAlg (E := E) A (polyStructureRing P n)

abbrev polyTopology (n : ℕ) := flatTopology P (polyCompletion P n) (polyCutoff P n)

theorem coefficientPresentable : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (E.CAlg A) := E.presentable A

abbrev polySections (n : ℕ) :=
  Sheaves.derivedGlobalSectionsCAlg (E := E) (polyTopology P n) A
    (Sheaves.sheafification_exists_cAlg (E := E) (polyTopology P n) A (coefficientPresentable (E := E) (A := A)))
    (coefficientPresentable (E := E) (A := A)) (polyStructure (E := E) P n)

/-- 概要：Δ_0(P) := Δ_{P^∧/A}（Not 4.16、CAlg 値）：平坦位相の site (P^∧/A)_Δ 上の O_Δ の CAlg 値 RΓ。
方針：A0 の `structurePresheaf` を `ringPresheafToCAlg` で CAlg 値にし、`derivedGlobalSectionsCAlg`。(p,d) 完備（Čech–Alexander の各項が完備、
極限で閉じる）。
規約：層化と presentable 性は入力（S4・G12）。
使われ方：Kan 延長の始域の値。 -/
def prismaticCohomologyCAlg (hP : IsBoundedPrism P) (n : ℕ) : (CompleteCAlg (E := E) P) _⦋0⦌ :=
  ⟨polySections (E := E) P n, by
    sorry⟩ -- Cor 3.12(d)：Čech 模型の完備な各項の極限は (p,d) 完備

def polySectionsCone (hP : IsBoundedPrism P) (n : ℕ) :
    { c : JoinCone (polyStructure (E := E) P n) // IsLimitCone c ∧ c.vertex = polySections (E := E) P n } := by
  sorry -- Cor 3.12(d)、isSheaf_iff_forget と derivedGlobalSections_of_isSheaf で層化単位に沿って移送

/-- 多項式上での第0脚。後の A5 では多項式分解の評価を延長する。 -/
def polySectionsProjection (hP : IsBoundedPrism P) (n : ℕ)
    (X : (PrismaticSite P (polyCompletion P n) (polyCutoff P n))ᵒᵖ) :=
  F2.nativeConeLeg (polySectionsCone (E := E) P hP n).val (ULift.up (nerveVertex X))

/-- 概要：Δ_0 は Čech–Alexander 模型の Tot_{E∞}（E∞ 代数として）。
方針：Cor 3.12 の CAlg 版（`isSheaf_iff_forget`）、脚注 10 の CAlg 版（`derivedGlobalSectionsCAlg_eq_totEInfinity`）。
規約：Rem 4.19 の小さい模型でも大きい模型でもよい。
使われ方：A1 の模型の環構造との一致（D27）、Δ_0 の関手性の具体形。 -/
theorem prismaticCohomologyCAlg_eq_totEInfinity (hP : IsBoundedPrism P) (n : ℕ) :
    Nonempty (VertexIso (polySections (E := E) P n) (Cosimplicial.totEInfinity (E := E) A (polyCosimplicialAlgebra P hP n))) := by
  sorry -- 要確認：Shared/CosimplicialEInfinity の totEInfinity_isLimitCone 待ち。
        -- Rem 4.19 の標準余積と S3 で同じ CAlg_A 図式上の極限錐を比較

abbrev polyTest (n : ℕ) (b : (PrismaticSite P (polyCompletion P n) (polyCutoff P n))ᵒᵖ) :=
  (equivSmallModel (PrismOver P (polyCompletion P n) (polyCutoff P n))).inverse.obj b.unop.unop

def polyFiberIso (n : ℕ) (b : (PrismaticSite P (polyCompletion P n) (polyCutoff P n))ᵒᵖ) :
    VertexIso ((polyStructure (E := E) P n).app _ (ULift.up (nerveVertex b)))
      ((E.discrete A).app _ (nerveVertex ((polyStructureRing P n).obj b))) := by
  sorry -- S2 ringPresheafToCAlg の指定した環での評価

def polyEval (hP : IsBoundedPrism P) (n : ℕ) (b : (PrismaticSite P (polyCompletion P n) (polyCutoff P n))ᵒᵖ) :=
  eqToHom (congrArg HomotopyCategory.mk (polySectionsCone (E := E) P hP n).property.2.symm) ≫
    SSet.Truncated.HomotopyCategory.homMk (polySectionsProjection (E := E) P hP n b) ≫ (polyFiberIso (E := E) P n b).hom

/-- 概要：Δ_0 : N(Poly k) → 𝒱（多項式代数の射 P → P′ についての関手性）。
方針：k 代数の射 P → P′ は P′^∧ 上の site から P^∧ 上の site への関手（prism B と R′ → B/dB から R → R′ → B/dB）を誘導し、RΓ の関手性
（S2 の `derivedGlobalSections_map` の CAlg 版）。∞ 関手としての coherent 性は、Čech–Alexander 模型の厳密な関手性（大きい模型、A0 の
Constr 4.18）から nerve で。
規約：持ち上げた形状 `uliftFunctor.obj (polyNerve k)` から。
使われ方：Kan 延長の入力。 -/
structure PolyDeltaData (hP : IsBoundedPrism P) where
  val : (SSet.uliftFunctor.{u+1,u}).obj (polyNerve (A ⧸ P.ideal)) ⟶ CompleteCAlg (E := E) P
  obj_eq (Q : Poly (A ⧸ P.ideal)) : val.app _ (ULift.up (nerveVertex Q)) = prismaticCohomologyCAlg (E := E) P hP Q.n
  map_eval {Q Q' : Poly (A ⧸ P.ideal)} (f : Q ⟶ Q')
      (b : (PrismaticSite P (polyCompletion P Q.n) (polyCutoff P Q.n))ᵒᵖ)
      (b' : (PrismaticSite P (polyCompletion P Q'.n) (polyCutoff P Q'.n))ᵒᵖ)
      (g : OrientedPrism.Hom (polyTest P Q.n b).Q (polyTest P Q'.n b').Q)
      (hg : g.comp (polyTest P Q.n b).toHom = (polyTest P Q'.n b').toHom)
      (_ : g.quotientMap.comp ((polyTest P Q.n b).sec.comp (prismPolynomialUnit P (Fin Q.n))) =
        (polyTest P Q'.n b').sec.comp ((prismPolynomialUnit P (Fin Q'.n)).comp f.toRingHom)) :
    let D := val ≫ prismCompleteInclusion (E := E) P
    let β : (polyStructureRing P Q.n).obj b ⟶ (polyStructureRing P Q'.n).obj b' :=
      Under.homMk (CommRingCat.ofHom g.toRingHom) (by sorry) -- hg の台の環射の等式
    let transport (U : Poly (A ⧸ P.ideal)) :=
      eqToHom (congrArg (fun v => HomotopyCategory.mk ((prismCompleteInclusion (E := E) P).app _ v)) (obj_eq U))
    transport Q ≫ polyEval (E := E) P hP Q.n b ≫
      SSet.Truncated.HomotopyCategory.homMk ((nerve.edgeMk β).map (E.discrete A)).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk
        ((uliftEdge (nerve.edgeMk f).toTruncated).map ((truncation 2).map D)) ≫ transport Q' ≫ polyEval (E := E) P hP Q'.n b'

def polyDeltaData (hP : IsBoundedPrism P) : PolyDeltaData (E := E) P hP := by
  sorry -- 要確認：A0/S2 へ。site の R からの構造射を多項式準同型で前合成。共通 cutoff での RΓ の関手性から
        -- 全単体の合成を得る。map_eval は同じ構造前層の制限を評価した可換四角形

def prismaticCohomologyPolyFunctor (hP : IsBoundedPrism P := by assumption) := (polyDeltaData (E := E) P hP).val

abbrev polyUnderlying (hP : IsBoundedPrism P) := prismaticCohomologyPolyFunctor (E := E) P hP ≫ prismCompleteInclusion (E := E) P
abbrev prismRestriction := cAlgRestrictScalars (E := E) P.deltaStructure.frobeniusLift

/-- 概要：Poly 上の Frobenius φ : Δ_0 → φ_{A*} ∘ Δ_0（φ_A 半線形）。
方針：A0 の `structurePresheafFrobenius` の CAlg 版と RΓ の関手性。
規約：φ_{A*} はスカラー制限（CAlg_A 上の関手、G-A2-5）。
使われ方：Frobenius の Kan 延長。 -/
def polyTestFrobenius (n : ℕ) (b : (PrismaticSite P (polyCompletion P n) (polyCutoff P n))ᵒᵖ) := by
  let U := (polyStructureRing P n).obj b
  let φ := P.deltaStructure.frobeniusLift
  let Uφ : A_R A := Under.mk (CommRingCat.ofHom (U.hom.hom.comp φ))
  let g : U ⟶ Uφ := Under.homMk (CommRingCat.ofHom (polyTest P n b).Q.deltaStructure.frobeniusLift)
    (by sorry) -- toHom は Frobenius と可換
  exact SSet.Truncated.HomotopyCategory.homMk ((nerve.edgeMk g).map (E.discrete A)).toTruncated ≫
    (cAlgRestrictScalars_algebraEmbedding (E := E) φ U).hom

def polyFrobeniusData (hP : IsBoundedPrism P) :
    { e : ((ihom ((SSet.uliftFunctor.{u+1,u}).obj (polyNerve (A ⧸ P.ideal)))).obj (E.CAlg A)).Edge
        (functorVertex (polyUnderlying (E := E) P hP)) (functorVertex (polyUnderlying (E := E) P hP ≫ prismRestriction (E := E) P)) //
      ∀ (Q : Poly (A ⧸ P.ideal)) (b : (PrismaticSite P (polyCompletion P Q.n) (polyCutoff P Q.n))ᵒᵖ),
        let x := ULift.up (nerveVertex Q)
        let π := eqToHom (congrArg (fun v => HomotopyCategory.mk ((prismCompleteInclusion (E := E) P).app _ v))
          ((polyDeltaData (E := E) P hP).obj_eq Q)) ≫ polyEval (E := E) P hP Q.n b
        π ≫ polyTestFrobenius (E := E) P Q.n b =
          functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) x ≫
            (hoFunctor.map (prismRestriction (E := E) P)).toFunctor.map π } := by
  sorry -- structurePresheafFrobenius と RΓ 射影の自然性、cAlgRestrictScalars_algebraEmbedding

def prismaticFrobeniusPoly (hP : IsBoundedPrism P) := (polyFrobeniusData (E := E) P hP).val

/-! ## 左 Kan 延長（Construction 7.6） -/

/-- 概要：導来 prismatic コホモロジー R ↦ Δ_{R/A}：Δ_0 の sifted 余極限保存な延長 P_Σ(N(Poly k)) → 𝒱（HTT 5.5.8.15）。
方針：A2-1 の `exists_siftedExtension` で選ぶ。
規約：選択を含む（sifted 余極限保存な延長は同値を除いて一意）。
使われ方：以下の全て。 -/
def derivedPrismaticCohomology (hP : IsBoundedPrism P := by assumption) : AnimatedAlgebra (A ⧸ P.ideal) ⟶ CompleteCAlg (E := E) P :=
  siftedLan _ (completeCAlg_siftedColimits (E := E) P) (prismaticCohomologyPolyFunctor (E := E) P hP)

theorem derivedPrismaticCohomology_preservesSifted (hP : IsBoundedPrism P) :
    PreservesSmallSiftedColimits (derivedPrismaticCohomology (E := E) P hP) :=
  (exists_siftedExtension _ (completeCAlg_siftedColimits (E := E) P) (prismaticCohomologyPolyFunctor (E := E) P hP)).choose_spec.1

def polyRecovery (hP : IsBoundedPrism P) :=
  siftedLanIso _ (completeCAlg_siftedColimits (E := E) P) (prismaticCohomologyPolyFunctor (E := E) P hP)

/-- 概要：(1)：多項式代数 j(P) での値は Δ_0(P)（充満忠実な包含に沿う Kan 延長の制限）。
方針：HTT 4.3.2.17（充満忠実な関手に沿う左 Kan 延長は元の関手を復元）、`exists_siftedExtension` の仕様。
規約：同値（頂点の同型）。
使われ方：A0・A1 の結果を導来版へ。 -/
def derivedPrismaticCohomology_poly (hP : IsBoundedPrism P) (n : ℕ) :
    let j := polyYoneda (A ⧸ P.ideal)
    let x := ULift.up (nerveVertex (⟨n⟩ : Poly (A ⧸ P.ideal)))
    VertexIso ((j ≫ derivedPrismaticCohomology (E := E) P hP).app _ x) (prismaticCohomologyCAlg (E := E) P hP n) :=
  (polyRecovery (E := E) P hP).app _ ≪≫ eqToIso (congrArg HomotopyCategory.mk ((polyDeltaData (E := E) P hP).obj_eq ⟨n⟩))

abbrev deltaUnderlying (hP : IsBoundedPrism P) := derivedPrismaticCohomology (E := E) P hP ≫ prismCompleteInclusion (E := E) P

/-- 概要：Frobenius φ : Δ → φ_{A*} ∘ Δ（Poly 上の φ の Kan 延長）。
方針：φ_{A*} は CAlg_A の **sifted** 余極限を保つ（全余極限ではない：初期対象は保たれない、W9-I-27）ので、両辺とも sifted 余極限保存。
完備版では (p,d) と (p,φ(d)) が同じ位相なのでスカラー制限は完備対象を保つ。Poly 上の自然変換の延長（HTT 5.5.8.15 の関手 ∞ 圏の同値）。
規約：—
使われ方：A4（Def 8.2 の φ 余極限）。 -/
def frobeniusExtension (hP : IsBoundedPrism P) :
    let k := A ⧸ P.ideal
    let H := deltaUnderlying (E := E) P hP
    let res := prismRestriction (E := E) P
    { e : ((ihom (AnimatedAlgebra k)).obj (E.CAlg A)).Edge (functorVertex H) (functorVertex (H ≫ res)) //
      let ρ := (polyRecovery (E := E) P hP).postcomp (prismCompleteInclusion (E := E) P)
      F2.Presentable.precomposeFunctorHom (polyYoneda k)
        (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫ (ρ.postcomp res).hom =
        ρ.hom ≫ SSet.Truncated.HomotopyCategory.homMk (prismaticFrobeniusPoly (E := E) P hP).toTruncated } := by
  sorry -- 完備圏内で siftedRestriction_equivalence の充満忠実性を使い包含で送る。
        -- φ_* は sifted 余極限を保ち、(p,d) と (p,φ(d)) の根基一致で完備化と両立

def derivedPrismaticFrobenius (hP : IsBoundedPrism P) := (frobeniusExtension (E := E) P hP).val

/-- 概要：離散 k 代数 R の Δ_R := Δ ∘ discreteToAnimated。E3 の `perfd` の材料。
方針：A2-1 の `discreteToAnimated`。
規約：E3 の始域 `algebraNerve` と同じ添字。
使われ方：A4。 -/
def derivedPrismaticCohomologyDiscrete (hP : IsBoundedPrism P := by assumption) :
    nerve (Under (CommRingCat.of (A ⧸ P.ideal))) ⟶ CompleteCAlg (E := E) P :=
  discreteToAnimated (A ⧸ P.ideal) ≫ derivedPrismaticCohomology (E := E) P hP

/-- 概要：D(A) 値の Δ（忘却）。A0 の `prismaticCohomology` と多項式代数で一致（`forget_derivedGlobalSections`）。
方針：U で後合成。
規約：—
使われ方：E3 の D(R) 版、HT filtration（D(A) で述べる）。 -/
def derivedPrismaticCohomologyDerived (hP : IsBoundedPrism P) :
    AnimatedAlgebra (A ⧸ P.ideal) ⟶ derivedInfinityCategory A :=
  deltaUnderlying (E := E) P hP ≫ E.forget A

def discreteFrobeniusComponent (hP : IsBoundedPrism P) (U : A_R (A ⧸ P.ideal)) :=
  (derivedPrismaticFrobenius (E := E) P hP).map (evaluateFunctorAt ((discreteToAnimated _).app _ (nerveVertex U)))

section Evaluation
variable (S : Type u) [CommRing S] [Algebra (A ⧸ P.ideal) S] (κ : Cardinal.{u})
  [EssentiallySmall.{u} (PrismOver P S κ)]

abbrev testStructure := Sheaves.ringPresheafToCAlg (E := E) A (testSiteRings P S κ)

/-- 離散代数値の O の Frobenius。係数射を φ_A と合成して A 線形な射にする。 -/
def testStructureFrobenius :
    FunctorHom (testStructure (E := E) P S κ) (testStructure (E := E) P S κ ≫ prismRestriction (E := E) P) := by
  sorry -- structurePresheafFrobenius と cAlgRestrictScalars_algebraEmbedding。
        -- 成分は小さい模型に対応する試験 prism B の φ_B

/-- 多項式分解から得た Δ_S を頂点にもつ評価錐。完全 site にはこの錐を制限する。
各脚は RΓ の評価から誘導され、一般の離散 S に対してこの錐の極限性を使わない。 -/
def discreteEvaluation (hP : IsBoundedPrism P) :
    let U := ofAlgebra (A ⧸ P.ideal) S
    let x := (derivedPrismaticCohomologyDiscrete (E := E) P hP ≫ prismCompleteInclusion (E := E) P).app _ (nerveVertex U)
    Σ c : JoinCone (testStructure (E := E) P S κ), { v : VertexIso x c.vertex //
      ∀ b : (PrismaticSite P S κ)ᵒᵖ,
        let t := ULift.up (nerveVertex b)
        let π := v.hom ≫ SSet.Truncated.HomotopyCategory.homMk (F2.nativeConeLeg c t)
        π ≫ functorHomEvaluate (testStructureFrobenius (E := E) P S κ) t =
          SSet.Truncated.HomotopyCategory.homMk (discreteFrobeniusComponent (E := E) P hP U).toTruncated ≫
            (hoFunctor.map (prismRestriction (E := E) P)).toFunctor.map π } := by
  sorry -- 各多項式→S→B/d に対する polySectionsProjection を sifted 表示で合わせる。
        -- 任意の B は共通 cutoff へ移して評価。Frobenius 両立は同じ RΓ 射影の自然性
end Evaluation

/-- 任意の完全 prism と B/d≃R に対する Def 8.2 の計算の入口。
A4 の restrictionSequence をここに逆 import しないため、塔を指定された全頂点・後続辺で受ける。 -/
def perfdValueOverPrism (hP : IsBoundedPrism P) (_ : P.deltaStructure.IsPerfect)
    {R : Type u} [CommRing R] (e : A ⧸ P.ideal ≃+* R) (S : A_R R) :
    (E.CAlg R) _⦋0⦌ := by
  let U := (Under.map (CommRingCat.ofHom e.toRingHom)).obj S
  let φ := discreteFrobeniusComponent (E := E) P hP U
  let τ := prismRestriction (E := E) P
  let iter : ℕ → (E.CAlg A ⟶ E.CAlg A) := Nat.rec (𝟙 _) (fun _ G => τ ≫ G)
  let T := Classical.choose (show ∃ D : (SSet.uliftFunctor.{u+1,0}).obj (nerve ℕ) ⟶ E.CAlg A,
    (∀ n : ℕ, D.app _ (ULift.up (nerveVertex n)) =
      (iter n).app _ ((derivedPrismaticCohomologyDiscrete (E := E) P hP ≫ prismCompleteInclusion (E := E) P).app _ (nerveVertex U))) ∧
    (∀ n : ℕ, D.app _ (ULift.up (ComposableArrows.mk₁ (homOfLE (Nat.le_succ n)))) =
      (φ.map (iter n)).edge) from by sorry) -- 後続辺の自由な合成から ℕ の図式を選ぶ
  have h : HasColimit T := by sorry -- CAlg_A は小さい逐次余極限をもつ
  exact (prismCompletion (E := E) P ≫ prismCompleteInclusion (E := E) P ≫ prismModIdeal (E := E) P ≫
    cAlgBaseChange (E := E) e.toRingHom).app _ h.choose.vertex

/-- 概要：H⁰(Δ_R) の環構造（CAlg 値なので H⁰ は可換環）と、A3 の Lemma 7.7(1) の準備（離散なら δ 構造）。
方針：E∞ 代数の H⁰ は可換環（EInfinity の H⁰ の環構造、E3 の `H0RingData` と同じ）。
規約：—
使われ方：A3、E3 の `h0`。 -/
def derivedPrismaticCohomology_h0_ring (hP : IsBoundedPrism P) (X : (AnimatedAlgebra (A ⧸ P.ideal)) _⦋0⦌) : A_R A := (E.pi0 A).obj (SSet.HomotopyCategory.mk ((deltaUnderlying (E := E) P hP).app _ X))

end SerrePositivity.BhattScholze.Prismatic
