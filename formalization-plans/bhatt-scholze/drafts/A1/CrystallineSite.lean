-- 将来の置き場所：SerrePositivity.BhattScholze.Crystalline.Site（仮。BS 著者版 Thm 5.2 の証明の big crystalline site [Ber06 §III.4] の affine 版）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §11（結晶 site（最小限）、2026-11-07）、単位 A1-6。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBaseRestriction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineResidueAlgebra
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineTower
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSitePullback
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteSmall
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteZariski
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSmallSiteTopology
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSmallStructureSheaf

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.Localization.Away.Basic
-- 本ファイルは drafts/Sheaves/{SheafCondition,GlobalSections,CechConerveLimit,CAlgValued}.lean、drafts/A0/PrismaticSite.lean（`cutoff`）、
-- drafts/Shared/CosimplicialEInfinity.lean（`totEInfinity`・`totEInfinity_map`・`derivedGlobalSectionsCAlg_eq_totEInfinity`）、
-- drafts/DerivedGeneral/ScalarRestriction.lean（`cAlgRestrictScalars`）、drafts/A2/DerivedPrismaticCohomology.lean（`coefficientPresentable`・
-- `polySections`・`polyCosimplicialAlgebra`・`prismaticCohomologyCAlg_eq_totEInfinity`）、drafts/A1/CrystallineInput.lean（`pdCechNerve`・
-- `pdCechAugmentation`・`pdFrameEval`・`exists_completedPDEnvelope`・`pdModel_iso_pdCechNerve`・`pdDeRhamFunctorIso`・`formsVertex`・`polyPoint`・
-- `deltaCopies`・`pdDeltaModel`・`crystallineBridge`・`crystallineBasePrism`・`crystallineBaseBounded`・`crystallineBase_generator`）、
-- drafts/A0/PrismaticEnvelope.lean（`completedFreeDelta`・`completedFreeDeltaBase`、`IsPrismaticEnvelope.lift`）を import する。
-- 順序：A1/CrystallineInput の後、A1/HodgeTateComparison・A1/DeRhamComparisonPoly の前（drafts/README の DAG）。

/-!
# 結晶 site（最小限）：affine な big crystalline site とその RΓ_crys（BS 著者版 Theorem 5.2・Theorem 6.4 の証明で使う形）

## 概要
**11-07 の方針変更（ユーザー）**：D25（Thm 5.2 を β 形で述べ RΓ_crys を定義しない）を改め、Berthelot の結晶 site を必要最小限で原典どおりに定義する。
基底は pd 環 (k, J, γ)（p ∈ J）、R̄ は k/J 代数。site (R̄/k)_CRYS の対象は (B, J_B, δ, R̄ → B/J_B)：k 代数 B、J_B 上の divided powers δ、
k → B は pd 射 (J, γ) → (J_B, δ)、p は B で冪零、R̄ → B/J_B は k/J 代数の射（BS 著者版 Theorem 5.2 の証明の「big crystalline site (R/A)_CRYS
as in [Ber06, §III.4]」の affine な対象。Stacks Tag 07HM の CRIS(C/A)）。位相は Zariski（B → B_{f_i}、(f_i) = B）。構造層 O_crys(B) = B、
RΓ_crys(R̄/k) := RΓ((R̄/k)_CRYS, O_crys)（CAlg_k 値、Sheaves の `derivedGlobalSectionsCAlg`）。
置く定理：(a) Čech–Alexander 型の計算（弱終な pro 対象 {D_S/p^e}、`crystallineCechIso`）、(b) 多項式の場合の Poincaré 補題
（`crystallineCohomology_polynomial_deRham`）、(c) Thm 5.2 の多項式の場合（`crystallineComparison_polynomial`。比較写像は原典の η
（`etaBridge`、b ↦ φ(b)、δ 変数つきの D^• = B^•{φ(J₀)/p}^∧）で、D68 の `crystallineBridge` はその (ℤ_p, (p)) の場合：`crystallineBridge_eq_eta`）、
(d) R̄ と基底についての site の関手性と、模型の射との一致（`crystallineCohomology_map`・`crystallineCohomology_map_frame`・
`crystallineCohomology_baseChangeEdge`）。
11-07 の決定（design-status §0.3.1 の末尾、a1-design §11.6）：affine に限る・Zariski 位相・Thm 5.2 は原典の η の写像が同型という形・
∞ 関手としての RΓ_crys は置かない・`pdCechNerveMap_quasiIso` は主張を残し証明を site 経由に・対象は p 冪零。

## 方針
A0 の prismatic site（`PrismOver`・`flatTopology`・cutoff κ・`SmallModel`）と同じ作り。site の公理は Zariski 被覆を生成系にした最小の Grothendieck
位相で避け、O_crys が層であることを定理にする（`crystallineStructure_isSheaf`）。層なので RΓ は O_crys 自身の極限（chaotic 位相の RΓ と同じ、
S2 の `derivedGlobalSections_of_isSheaf`）。対象は p 冪零（Berthelot どおり）なので、弱終なのは pd 包の p 完備化 D そのものではなく pro 対象
{D/p^e}_e（BS 著者版 p.45–46 の記述、Stacks Tag 07HP・07JL）。そのため S3 の pro 版 `exists_limitCone_of_proCech`（本ファイルの Sheaves の節）を使う。
**関手性は big site だから厳密**：f : R̄ → R̄′ は (B, R̄′ → B/J_B) ↦ (B, R̄ → R̄′ → B/J_B) で CRYS(R̄′) → CRYS(R̄) を与える（小さい site Cris(R̄)
（R̄ ≅ B/J_B）ではこの関手がない）。

## 規約
affine な対象だけ（BS の Def 4.1 の prismatic site と同じ扱い）。κ は明示のパラメータ、`IsCrystallineCutoff`（κ ≥ `cutoff k R̄`）。値は CAlg_k。
Berthelot の「γ と両立」は、R̄ が k/J 代数で R̄ → B/J_B が k/J 線形なので J B ⊆ J_B となり、k → B が pd 射であることと同じ（Stacks の定義）。
∞ 関手としての RΓ_crys（Q ↦ RΓ_crys(Q/p)）は置かない：高次の整合性は厳密な模型（A1/DeRhamComparisonPoly の `wittBigPdModel`）から来て、
site の関手性はその頂点と辺の意味（(a)(d)）を与える（a1-design §11.4）。

## 使われ方
A1/DeRhamComparisonPoly（D69）：`wittSmallBridge_isInvertible` は Cor 4.12（`psiBaseChange`）と (c) を (W(C), J) で（`frobeniusPdBridge_tot` で
X ↦ X^p の形に読む）、`wittBigBridge_isInvertible`・
`wittSmallFrame_isInvertible` は (a) の自然性（(d)）で、段 4 の各成分は (b) で読む（a1-design §11.3）。D68 の経路（A1/CrystallineInput の六段）は使わない。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial Cardinal

/-! ## S3 の pro 版（脚注 10 の pro 対象版。中身の段階で drafts/Sheaves/CechConerveLimit.lean へ移す） -/

namespace SerrePositivity.InfinityCategories.Sheaves

variable {𝒟 : Type u} [SmallCategory 𝒟] {E : SSet.{u + 1}} [Quasicategory E]

/-- 概要：塔 U : ℕ ⥤ 𝒟（U_e → U_{e+1}）が pro の意味で弱終：任意の対象 V から、ある U_e への射がある（BS 著者版 Theorem 5.2 の証明の
「weakly initial pro-object」を site の向きで。Stacks Tag 07HP）。
方針：`IsWeaklyTerminal` の pro 版。
規約：環の側では D/p^{e+1} → D/p^e が site の U_e → U_{e+1}。
使われ方：`exists_limitCone_of_proCech`、結晶 site の (a)。 -/
def IsProWeaklyTerminal (U : ℕ ⥤ 𝒟) : Prop := ∀ V : 𝒟, ∃ e : ℕ, Nonempty (V ⟶ U.obj e)

/-- 概要：塔の各段の Čech 脈体のデータと、段の間の単体的対象の射（射影と両立）。
方針：各段は S3 の `CechNerveData`。遷移は U_e^{(n)} → U_{e+1}^{(n)}。
規約：一般の積の存在は仮定しない（各段の積だけをデータで持つ）。
使われ方：`proCechShape`。 -/
structure ProCechNerveData (U : ℕ ⥤ 𝒟) where
  /-- 各段の Čech 脈体。 -/
  level : ∀ e : ℕ, CechNerveData (U.obj e)
  /-- 段の間の遷移。 -/
  transition : ∀ e : ℕ, (level e).obj ⟶ (level (e + 1)).obj
  /-- 遷移は射影と両立。 -/
  transition_proj : ∀ (e n : ℕ) (i : Fin (n + 1)),
    (transition e).app (Opposite.op ⦋n⦌) ≫ (level (e + 1)).proj n i =
      (level e).proj n i ≫ U.map (homOfLE (Nat.le_succ e))

/-- 概要：添字の関手 ℕᵒᵖ × Δ ⥤ 𝒟ᵒᵖ、(e, [n]) ↦ U_e^{(n)}。
方針：`Functor.ofSequence d.transition` を Δᵒᵖ について opposite にして uncurry。
規約：前層 F を合成すると (e, [n]) ↦ F(U_e^{(n)})（e について反変、[n] について余単体的）。
使われ方：`proCechShape`。 -/
def proCechIndexFunctor {U : ℕ ⥤ 𝒟} (d : ProCechNerveData U) : ℕᵒᵖ × SimplexCategory ⥤ 𝒟ᵒᵖ :=
  sorry -- Functor.ofSequence d.transition の各値の rightOp を並べて Functor.uncurry（ℕ の向きは op）

theorem proCechIndexFunctor_obj {U : ℕ ⥤ 𝒟} (d : ProCechNerveData U) (e : ℕ) (n : SimplexCategory) :
    (proCechIndexFunctor d).obj (Opposite.op e, n) = Opposite.op ((d.level e).obj.obj (Opposite.op n)) := by
  sorry -- Functor.ofSequence の対象と uncurry の定義

/-- 概要：pro Čech 脈体の形状 N(ℕᵒᵖ × Δ) → N(𝒟)^op（S3 の `cechShape` の pro 版）。
方針：`proCechIndexFunctor` の nerve を持ち上げる。
規約：始域は持ち上げた N(ℕᵒᵖ × Δ)。
使われ方：`exists_limitCone_of_proCech`。 -/
def proCechShape {U : ℕ ⥤ 𝒟} (d : ProCechNerveData U) :
    (SSet.uliftFunctor.{u + 1, 0}).obj (nerve (ℕᵒᵖ × SimplexCategory)) ⟶ presheafShape 𝒟 where
  app _ := ↾fun s => ⟨s.down ⋙ proCechIndexFunctor d⟩
  naturality _ _ _ := rfl

/-- 概要：脚注 10 の pro 版：U が pro の意味で弱終で各段が Čech 脈体なら、(e, [n]) ↦ F(U_e^{(n)}) の極限錐の頂点は F の極限（Γ(F)）の頂点。
方針：空間値前層で colim_e |h_{U_e^{(•)}}| → * が同値（各 V で、e が大きければ Hom(V, U_e) は空でなく、空でない集合の Čech 脈体の実現は可縮、
filtered 余極限は可縮）。重み付き極限（Sheaves/SpaceValued の `weightedSections`・`sectionsOf_colimit`）で lim F = lim_e lim_Δ F(U_e^{(•)})。
規約：F は前層でよい（位相は使わない）。E の極限の存在は仮定しない（錐 t の側に置く）。
使われ方：結晶 site の (a)（`crystallineCechIso`）。 -/
theorem exists_limitCone_of_proCech {U : ℕ ⥤ 𝒟} (hU : IsProWeaklyTerminal U) (d : ProCechNerveData U)
    (F : Presheaf 𝒟 E) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (proCechShape d ≫ F)) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = t.vertex := by
  sorry -- colim_e |h_{U_e^•}| ≃ * の重み付き極限（S8 の sectionsOf_colimit）と S3 の各段の比較

end SerrePositivity.InfinityCategories.Sheaves

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.DerivedCompletion SerrePositivity.DifferentialGraded
open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime]

/-! ## 対象と射（[Ber06 §III.4] の big crystalline site の affine な対象、Stacks Tag 07HM の CRIS(C/A)） -/

/-- BS 著者版 Theorem 6.4 の連続形式を厳密な cdga から実現する。 -/
def theoryFormsCAlg (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] :=
  Cosimplicial.strictShapeNerve (formsCDGAFunctor p k) ≫ E.ofCdga k

/-- Theorem 6.4 の形式関手の多項式頂点。 -/
abbrev theoryFormsVertex (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] (n : ℕ) :=
  (theoryFormsCAlg (E := E) p k).app _ (polyPoint k n)

/-- Theorem 6.4、D69 の段 6 の関手同型。厳密な二つの射影を同じ E で実現する。 -/
def theoryPdDeRhamFunctorIso (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k) ≫ E.ofCosimplicial k)
      (theoryFormsCAlg (E := E) p k) := by
  let disc := (Functor.whiskeringRight SimplexCategory _ _).obj
    (SerrePositivity.EInfinity.discreteCDGA k)
  let ev0 := (evaluation SimplexCategory (CommMon (Complex k))).obj ⦋0⦌
  let ea : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k ⋙ disc) ≫ E.ofCosimplicialCdga k)
      (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k) ≫ E.ofCosimplicial k) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
      ((E.ofCosimplicialCdga_discrete k).precomp
        (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k)))
      (by rw [Cosimplicial.strictShapeNerve_comp]; rfl) rfl
  let eb := Cosimplicial.strictNatTransFunctorIso (pdDeRhamProjection p k)
    (E.ofCosimplicialCdga k) (by
      sorry) -- 行 0 への射影の擬同型性は総複体で示す（pdRow_contractible）。
             -- ofCosimplicialCdga の射の忘却像を総複体の射と比較する作業が残る
  let ec : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (Cosimplicial.strictShapeNerve (pdDeRhamCDGA p k) ≫ E.ofCosimplicialCdga k)
      (Cosimplicial.strictShapeNerve (pdDeRhamCDGA p k ⋙ ev0) ≫ E.ofCdga k) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (Cosimplicial.strictShapeNerve (pdDeRhamCDGA p k))
        (E.ofCosimplicialCdga_evalZero k)) (by
          sorry)) -- 同じ指定錐の [0] の脚。pdDeRham_homotopicallyConstant を使う
      rfl (by rw [Cosimplicial.strictShapeNerve_comp]; rfl)
  let ed := Cosimplicial.strictNatTransFunctorIso (pdDeRhamZeroIso p k).hom (E.ofCdga k) (by
    sorry) -- 厳密な同型の成分なので nerve の辺は可逆
  exact ea.symm ≪≫ eb.symm ≪≫ ec ≪≫ ed

section Site

variable {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (Rbar : Type u) [CommRing Rbar] [Algebra (k ⧸ J) Rbar]

attribute [instance] CrysOver.ring CrysOver.alg

variable (κ : Cardinal.{u}) [EssentiallySmall.{u} (CrysOver p γ Rbar κ)]


/-- 概要：O_crys を CAlg_k 値前層として（離散埋め込み）。 -/
abbrev crystallineStructure := Sheaves.ringPresheafToCAlg (E := E) k (crystallineStructureRing p γ Rbar κ)

/-- 概要：RΓ_crys(R̄/k) := RΓ((R̄/k)_CRYS, O_crys)（CAlg_k 値。BS 著者版 Theorem 5.2 の RΓ_crys(R/A)、Theorem 6.4 の RΓ_crys((R/p)/W(A/I))）。
方針：Sheaves の `derivedGlobalSectionsCAlg`（層化と CAlg_k の presentable 性は A2 と同じ入力）。
規約：値は選んだ極限錐の頂点。使う側は (a) の同型と `crystallineCohomology_isLimit` で扱う。
使われ方：(a)〜(d)、A1/DeRhamComparisonPoly。 -/
def crystallineCohomology : (E.CAlg k) _⦋0⦌ :=
  Sheaves.derivedGlobalSectionsCAlg (E := E) (zariskiTopology p γ Rbar κ) k
    (Sheaves.sheafification_exists_cAlg (E := E) (zariskiTopology p γ Rbar κ) k (coefficientPresentable (E := E) (A := k)))
    (coefficientPresentable (E := E) (A := k)) (crystallineStructure (E := E) p γ Rbar κ)

/-- 概要：「高次コホモロジーは位相によらない」：RΓ_crys は O_crys 自身の極限錐の頂点（chaotic 位相の RΓ、Stacks Tag 07JK の C 上の RΓ と同じ）。
方針：`crystallineStructure_isSheaf` と S2 の `derivedGlobalSections_of_isSheaf`。
規約：頂点の等号。
使われ方：(a)、`crystallineCohomology_map`。 -/
theorem crystallineCohomology_isLimit :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (crystallineStructure (E := E) p γ Rbar κ), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = crystallineCohomology (E := E) p γ Rbar κ := by
  sorry -- derivedGlobalSections_of_isSheaf と crystallineStructure_isSheaf

end Site

/-! ## 関手性（(d)：R̄ について、基底について） -/

section Functoriality

variable {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable {Rbar Rbar' : Type u} [CommRing Rbar] [Algebra (k ⧸ J) Rbar] [CommRing Rbar'] [Algebra (k ⧸ J) Rbar'] (κ : Cardinal.{u})

variable [EssentiallySmall.{u} (CrysOver p γ Rbar κ)] [EssentiallySmall.{u} (CrysOver p γ Rbar' κ)]

/-- 概要：(d) の辺 RΓ_crys(R̄/k) → RΓ_crys(R̄′/k)：O_crys の CRYS(R̄) 上の極限を CRYS(R̄′) への制限に写す（BS 著者版 Theorem 6.4 の
「functorial isomorphism」の結晶側の関手性）。
方針：`crysPullbackSite` に沿う O_crys の制限は O_{R̄′}（台の環が同じ）。`crystallineCohomology_isLimit` の二つの極限錐の間の、
制限から来る比較の辺（極限の普遍性）。
規約：辺は CAlg_k の 1 単体。ホモトピー圏で関手的（`crystallineCohomology_map_comp`）。
使われ方：`crystallineCohomology_map_frame`、a1-design §11.4。 -/
def crystallineCohomology_map (f : Rbar →ₐ[k ⧸ J] Rbar') :
    SSet.Edge (crystallineCohomology (E := E) p γ Rbar κ) (crystallineCohomology (E := E) p γ Rbar' κ) := by
  sorry -- 制限した錐から極限錐への普遍性の辺（crystallineCohomology_isLimit を両側で）

/-- 概要：(d) の関手則（ホモトピー圏）：f の後に f′ の辺は f′ ∘ f の辺。
方針：`crysPullback` の関手則は厳密（rfl）なので、極限の普遍性の一意性（ホモトピー圏）から。
規約：ホモトピー圏の等式。∞ の高次の整合性は述べない（a1-design §11.4）。
使われ方：a1-design §11.4。 -/
theorem crystallineCohomology_map_comp {Rbar'' : Type u} [CommRing Rbar''] [Algebra (k ⧸ J) Rbar'']
    [EssentiallySmall.{u} (CrysOver p γ Rbar'' κ)] (f : Rbar →ₐ[k ⧸ J] Rbar') (f' : Rbar' →ₐ[k ⧸ J] Rbar'') :
    HomotopyCategory.homMk (crystallineCohomology_map (E := E) p γ κ f) ≫ HomotopyCategory.homMk (crystallineCohomology_map (E := E) p γ κ f') =
      HomotopyCategory.homMk (crystallineCohomology_map (E := E) p γ κ (f'.comp f)) := by
  sorry -- 引き戻しの合成は厳密に引き戻し。極限の普遍性の一意性

end Functoriality

section BaseChange

variable {k l : Type u} [CommRing k] [CommRing l] {J : Ideal k} {J' : Ideal l} (γ : DividedPowers J) (γ' : DividedPowers J')
variable (Rbar : Type u) [CommRing Rbar] [Algebra (k ⧸ J) Rbar] [Algebra (l ⧸ J') Rbar] (κ : Cardinal.{u})

variable [EssentiallySmall.{u} (CrysOver p γ Rbar κ)] [EssentiallySmall.{u} (CrysOver p γ' Rbar κ)]

/-- 概要：(d) の基底についての辺 RΓ_crys(R̄/k) → g_* RΓ_crys(R̄/l)（CAlg_k）。転置 completeChange g RΓ_crys(R̄/k) → RΓ_crys(R̄/l) は
A1/DeRhamComparisonPoly の `baseChangeTotEdge` と同じ随伴の転置（BS 著者版 Theorem 6.4 の「RΓ_crys((R/p)/W(A/I)) lifts Ω_{R/(A/I)}」の、
W(A/I) → A/I に沿う結晶コホモロジーの底変換）。
方針：`crysBaseRestriction` に沿う O_crys の制限は g_* O_crys（台の環が同じ）、極限の制限と `cAlgRestrictScalars` の極限保存（右随伴）。
規約：多項式の R̄ での可逆性は模型の定理 `pdModelBaseChange_isInvertible`（A1/DeRhamComparisonPoly）が担う（`crystallineCohomology_baseChange_frame`）。
使われ方：a1-design §11.3 の段 3。 -/
def crystallineCohomology_baseChangeEdge (g : k →+* l) (hg : DividedPowers.IsDPMorphism γ γ' g)
    (hR : (algebraMap (l ⧸ J') Rbar).comp ((Ideal.Quotient.mk J').comp g) =
      (algebraMap (k ⧸ J) Rbar).comp (Ideal.Quotient.mk J)) :
    SSet.Edge (crystallineCohomology (E := E) p γ Rbar κ)
      ((cAlgRestrictScalars (E := E) g).app _ (crystallineCohomology (E := E) p γ' Rbar κ)) := by
  sorry -- 制限した錐と cAlgRestrictScalars の極限保存（右随伴）。crystallineCohomology_isLimit を両側で

end BaseChange

/-! ## (a) Čech–Alexander 型の計算（BS 著者版 Theorem 5.2 の証明の pro 対象 {D/p^n}、Stacks Tag 07JN） -/

section Cech

variable {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J)
variable {Rbar : Type u} [CommRing Rbar] [Algebra (k ⧸ J) Rbar] (κ : Cardinal.{u})
variable [EssentiallySmall.{u} (CrysOver p γ Rbar κ)]

/-- 概要：枠 s : S → R̄ の J つき pd Čech 脈体 D_S^• の各項の pd イデアルと divided powers（`pdCechNerve` の対象の選択と同じ選び方）。
方針：`exists_completedPDEnvelope` の選択の K′・δ を取り出す。
規約：`pdCechNerve` の構造射はこの divided powers について pd 射（`pdCechNerve_isDPMorphism`）。
使われ方：pro 対象の各段を site の対象にする、(d) の仮定。 -/
def pdCechNerveIdeal {S : Type u} (s : S → Rbar) (n : SimplexCategory) :
    letI := crysResidueAlgebra (J := J) (R := Rbar)
    Ideal ((pdCechNerve p γ hp (crysResidue_kernel (J := J) (R := Rbar)) s).obj n).right := by
  sorry -- pdCechNerve.obj と同じ exists_completedPDEnvelope の選択の K′

def pdCechNerveDP {S : Type u} (s : S → Rbar) (n : SimplexCategory) :
    DividedPowers (pdCechNerveIdeal p γ hp s n) := by
  sorry -- 同じ選択の δ

theorem pdCechNerve_isDPMorphism {S : Type u} (s : S → Rbar) {m n : SimplexCategory} (θ : m ⟶ n) :
    letI := crysResidueAlgebra (J := J) (R := Rbar)
    DividedPowers.IsDPMorphism (pdCechNerveDP p γ hp s m) (pdCechNerveDP p γ hp s n)
      ((pdCechNerve p γ hp (crysResidue_kernel (J := J) (R := Rbar)) s).map θ).right.hom := by
  sorry -- 構造射は IsCompletedPDEnvelope.lift の pd 射

/-- 概要：Tot と p 進の塔の極限：各項が p 進完備な余単体的 k 代数 X について、(e, [n]) ↦ X^n/p^{e+1} の CAlg_k 上の極限は Tot_{E∞} X
（Stacks Tag 07JL：遷移が全射なので R¹lim = 0）。
方針：Δ と ℕᵒᵖ の極限の交換、各 n で lim_e X^n/p^{e+1} = X^n（完備）で遷移は全射（Mittag-Leffler）、`totEInfinity_isLimitCone`。
規約：X の項の p 進完備性は仮定。
使われ方：`crystallineCechIso`。 -/
theorem totEInfinity_isLimit_truncations (X : Cosimplicial.CosimplicialAlgebra k)
    (hX : ∀ n : SimplexCategory, IsAdicComplete (Ideal.span {(p : (X.obj n).right)}) (X.obj n).right)
    (D : (SSet.uliftFunctor.{u + 1, 0}).obj (nerve (ℕᵒᵖ × SimplexCategory)) ⟶ E.CAlg k)
    (hD : ∀ (e : ℕ) (n : SimplexCategory), Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (D.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Opposite.op e, n))))
      ((E.discrete k).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {(p : (X.obj n).right) ^ (e + 1)})).comp (X.obj n).hom.hom))))))) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ∧ c.vertex = Cosimplicial.totEInfinity (E := E) k X := by
  sorry -- Δ × ℕᵒᵖ の極限を Δ ごとに取り、各項の lim_e は Mittag-Leffler で X^n。totEInfinity_isLimitCone

/-- 概要：**(a)** Čech–Alexander 型の計算：全射な枠 s : S → R̄ について RΓ_crys(R̄/k) ≃ Tot_{E∞} D_S^•（BS 著者版 Theorem 5.2 の証明の
「RΓ_crys(R/A) is computed by the cosimplicial ring D^•」、Stacks Tag 07JN の F = O の場合）。
方針：`crystallineCohomology_isLimit`（O_crys は層なので RΓ = lim O）、`pdCechTower`・`pdCechTower_proWeaklyTerminal` と
`exists_limitCone_of_proCech`（O の pro Čech 図式の極限 ＝ lim O）、`totEInfinity_isLimit_truncations`（その極限 ＝ Tot D_S^•、各項は
`IsCompletedPDEnvelope.complete` で p 進完備）。
規約：k は p 進完備。CAlg_k の頂点の同型（選んだもの）。D69 の大きい枠（S = Q^∧）と小さい枠（S = Fin r）の両方に使う。
使われ方：(b)・(c)・(d)、A1/DeRhamComparisonPoly の `wittBigPdModel`・`pdModel` が RΓ_crys を計算することの根拠。 -/
def crystallineCechIso {S : Type u} (s : S → Rbar)
    (hs : letI := crysResidueAlgebra (J := J) (R := Rbar); Function.Surjective (pdFrameEval (k := k) s 0))
    (hk : IsAdicComplete (Ideal.span {(p : k)}) k) (hκ : IsCrystallineCutoff k Rbar κ) (hS : Cardinal.mk S ≤ κ) :
    letI := crysResidueAlgebra (J := J) (R := Rbar)
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (crystallineCohomology (E := E) p γ Rbar κ)
      (Cosimplicial.totEInfinity (E := E) k (pdCechNerve p γ hp (crysResidue_kernel (J := J) (R := Rbar)) s)) := by
  sorry -- crystallineCohomology_isLimit・exists_limitCone_of_proCech（pdCechTower）・totEInfinity_isLimit_truncations の三つの極限錐の比較

/-- 概要：**(d)** site の関手性と模型の射の一致：f : R̄ → R̄′、全射な枠 s・s′ と、余単体的 k 代数の射 m : D_S^• → D_{S′}^• が各項で
pd 射で増大について f と両立するなら、(a) の同型のもとで `crystallineCohomology_map f` は Tot_{E∞} m（ホモトピー圏の可換な四角形）。
方針：m の各段の mod p^{e+1} は pro 対象の間の site の射（pd 射・sec と両立）で、O_crys の極限の制限は pro Čech 図式の上で m に一致（S3 の
制限の自然性）。`crystallineCechIso` の構成の三つの極限錐がそれぞれ自然。
規約：m は任意（普遍性の lift でなくてよい）。BS 著者版 Theorem 5.2 の「this recipe is independent of the choice of (B₀ → R) up to canonical
isomorphism」は R̄ = R̄′、f = id の場合（枠の取り替えが Tot で可逆、`pdCechNerveMap_quasiIso` を site から）。
使われ方：A1/DeRhamComparisonPoly の各対象での可逆性（`wittSmallFrame_isInvertible`、段 2・3 の四角形）、a1-design §11.3・§11.4。 -/
theorem crystallineCohomology_map_frame {Rbar' : Type u} [CommRing Rbar'] [Algebra (k ⧸ J) Rbar'] [EssentiallySmall.{u} (CrysOver p γ Rbar' κ)]
    (f : Rbar →ₐ[k ⧸ J] Rbar') {S S' : Type u} (s : S → Rbar) (s' : S' → Rbar')
    (hs : letI := crysResidueAlgebra (J := J) (R := Rbar); Function.Surjective (pdFrameEval (k := k) s 0))
    (hs' : letI := crysResidueAlgebra (J := J) (R := Rbar'); Function.Surjective (pdFrameEval (k := k) s' 0))
    (hk : IsAdicComplete (Ideal.span {(p : k)}) k) (hκ : IsCrystallineCutoff k Rbar κ) (hκ' : IsCrystallineCutoff k Rbar' κ)
    (hS : Cardinal.mk S ≤ κ) (hS' : Cardinal.mk S' ≤ κ)
    (m : (letI := crysResidueAlgebra (J := J) (R := Rbar); pdCechNerve p γ hp (crysResidue_kernel (J := J) (R := Rbar)) s) ⟶
      (letI := crysResidueAlgebra (J := J) (R := Rbar'); pdCechNerve p γ hp (crysResidue_kernel (J := J) (R := Rbar')) s'))
    (hm_dp : ∀ n : SimplexCategory, DividedPowers.IsDPMorphism (pdCechNerveDP p γ hp s n) (pdCechNerveDP p γ hp s' n)
      (m.app n).right.hom)
    (hm_aug : ∀ x, (letI := crysResidueAlgebra (J := J) (R := Rbar'); pdCechAugmentation p γ hp (crysResidue_kernel (J := J) (R := Rbar')) s')
      ((m.app ⦋0⦌).right.hom x) =
        f ((letI := crysResidueAlgebra (J := J) (R := Rbar); pdCechAugmentation p γ hp (crysResidue_kernel (J := J) (R := Rbar)) s) x)) :
    HomotopyCategory.homMk (crystallineCohomology_map (E := E) p γ κ f) ≫ (crystallineCechIso (E := E) p γ hp κ s' hs' hk hκ' hS').hom =
      (crystallineCechIso (E := E) p γ hp κ s hs hk hκ hS).hom ≫ HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) k m) := by
  sorry -- m の mod p^{e+1} は pro 対象の site の射。O の極限の制限と pro Čech 図式の上の m の比較（S3 の制限の自然性）

end Cech

/-! ## (b) 多項式の場合の Poincaré 補題（Stacks Tag 07LG の F = O、[Ber74 V.2.3.2]） -/

section Polynomial

variable {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J) (hp : (p : k) ∈ J) (κ : Cardinal.{u})

include hp in
/-- 概要：**(b)** R̄ = (k/J)[X_1,…,X_r] の持ち上げ k⟨X⟩ について RΓ_crys(R̄/k) ≃ Ω̂^•_{k⟨X⟩/k}（CAlg_k）。BS 著者版 Theorem 6.4 の証明の
「by generalities on crystalline cohomology, RΓ_crys lifts the de Rham complex」の多項式の場合。
方針：小さい枠 Fin r → R̄（j ↦ X_j）で (a)（`crystallineCechIso`）、`pdModel_iso_pdCechNerve`（D_{Fin r}^• = `pdModel k r`、J は k 上自由な D に
延びる）、`pdDeRhamFunctorIso` の成分（行 0 への射影は j ≥ 1 の行の収縮 `pdRow_contractible`、列 0 への射影は pd Poincaré
`pdDeRham_homotopicallyConstant`、Stacks Tag 07LA・07LD の二つの spectral sequence と同じ span）。
規約：k は p 進完備・p ねじれなし、γ は p 上で標準（n! γ_n(p) = p^n）。値は A1/CrystallineInput の `formsVertex`。
使われ方：A1-5 で k = C = A₀/d₀（J = (p)）、a1-design §11.3 の段 4。 -/
def crystallineCohomology_polynomial_deRham (γ : DividedPowers J) (hp : (p : k) ∈ J) (κ : Cardinal.{u}) (r : ℕ)
    (hγ : ∀ n : ℕ, (n.factorial : k) * γ.dpow n (p : k) = (p : k)^n)
    (hk : IsAdicComplete (Ideal.span {(p : k)}) k) (hreg : Function.Injective (fun x : k => (p : k) * x))
    [EssentiallySmall.{u} (CrysOver p γ (MvPolynomial (Fin r) (k ⧸ J)) κ)]
    (hκ : IsCrystallineCutoff k (MvPolynomial (Fin r) (k ⧸ J)) κ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (crystallineCohomology (E := E) p γ (MvPolynomial (Fin r) (k ⧸ J)) κ) (theoryFormsVertex (E := E) p k r) := by
  sorry -- crystallineCechIso（枠 X_j、#Fin r ≤ κ）≪≫ Tot の pdModel_iso_pdCechNerve ≪≫ (theoryPdDeRhamFunctorIso E p k).app (polyPoint k r)

end Polynomial

/-! ## (c) Theorem 5.2 の多項式の場合（BS 著者版 Theorem 5.2、R = (A/I)[X_1,…,X_r]。比較写像は原典の η） -/

section Comparison

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P) (hgen : P.generator = p)
variable {I : Ideal A} (γI : DividedPowers I) (hpI : (p : A) ∈ I) (κ : Cardinal.{u}) (r : ℕ)

/-- R̄ := (A/I)[X_1,…,X_r]。R^{(1)} = R̄ ⊗_{A/I, ψ} A/p = (A/p)[X] は A2 の `polyCompletion P r`（p = 0 なので完備化は自明）。 -/
abbrev crysPolynomial := MvPolynomial (Fin r) (A ⧸ I)

/-- 小さい枠 X_j の J つき pd Čech 脈体（δ 変数なしの D^•、基底 (A, I, γ_I)）。(a)（`crystallineCechIso`）の右辺。 -/
abbrev polyPdCech : Cosimplicial.CosimplicialAlgebra A :=
  letI := crysResidueAlgebra (J := I) (R := crysPolynomial r (I := I))
  pdCechNerve p γI hpI (crysResidue_kernel (J := I) (R := crysPolynomial r (I := I)))
    (fun j : ULift.{u} (Fin r) => (MvPolynomial.X j.down : crysPolynomial r (I := I)))

/-- 概要：B^n = A{X_j^{(i)}}^∧（(n+1) 個の copy の変数の完備自由 δ-A 代数、A0 の `completedFreeDelta`）の変数 X_j^{(i)}（δ⁰ 座標）。
方針：A1/CrystallineInput の `deltaCopyX`（A = ℤ_p）と同じ式を一般の A で。
規約：copy の添字は A1/CrystallineInput の `deltaCopies r n`（= formVars r × Fin (n+1)）。
使われ方：`pdDeltaCechNerve`。 -/
def deltaCechVariable (n : ℕ) (a : deltaCopies.{u} r n) : completedFreeDelta P (deltaCopies.{u} r n) :=
  pdCompletionUnit (RelativeFreeDeltaRing (R := A) (deltaCopies.{u} r n)) p (algebraMap A _ P.generator)
    (MvPolynomial.X (a, 0))

/-- 概要：原典の δ 変数つきの D^•（BS 著者版 Theorem 5.2 の証明の D^•）：B^n = A{X^{(0)},…,X^{(n)}}^∧（`completedFreeDelta`）の
J₀^n = I B^n + (X_j^{(i)} − X_j^{(0)}) の、γ_I と両立する p 完備な pd 包。BS 著者版 Cor 2.39 の形で D^n = B^n{φ(J₀)/p}^∧。
方針：各項は `exists_completedPDEnvelope`（`pdCechNerve` と同じ選び方）、θ : [m] → [n] は copy の添字の写像の δ 射（自由 δ 環の普遍性）を
pd 包の普遍性で lift（map_id・map_comp は lift の一意性）。
規約：J₀ には δ^a(X)（a ≥ 1）の copy の差を入れない：R′ := B^0/J₀^0 = (A/I)[δ^a(X_j)] ≠ R̄ で、D^n は big site CRYS(R̄) の中で
(D^0, R̄ → R′ = D^0/J̄) の (n+1) 個の余積（R′ ⊗_{R̄} ⋯ ⊗_{R̄} R′ は高次座標について自由）。A = ℤ_p、I = (p) では A1/CrystallineInput の
`pdDeltaModel`（`crystallineBridge_eq_eta`）。D^n は p ねじれなしで δ 構造をもつ（BS 著者版 Lemma 2.38）。
使われ方：`etaBridge`・`pdDeltaRetraction`。 -/
def pdDeltaCechNerve : Cosimplicial.CosimplicialAlgebra A where
  obj n := by
    classical
    let B := completedFreeDelta P (deltaCopies.{u} r n.len)
    letI : Algebra A B := (completedFreeDeltaBase P _).toAlgebra
    let x (a : deltaCopies.{u} r n.len) : B := deltaCechVariable p P r n.len a
    let J₀ : Ideal B := I.map (algebraMap A B) ⊔
      Ideal.span (Set.range fun a : formVars.{u} r × Fin n.len => x (a.1, a.2.succ) - x (a.1, 0))
    have h := exists_completedPDEnvelope p γI hpI J₀ le_sup_left
    let D := h.choose
    letI : CommRing D := h.choose_spec.choose
    letI : Algebra A D := h.choose_spec.choose_spec.choose
    exact Under.mk (CommRingCat.ofHom (algebraMap A D))
  map θ := by sorry -- copy の添字の写像（自由 δ 環の δ 射）を pd 包の普遍性で lift。J₀ は J₀ へ
  map_id := by sorry -- lift の一意性
  map_comp := by sorry -- lift の一意性

include hgen in
/-- 概要：**(c) の比較写像（原典の η）**：Rem 4.19 の小さい Čech–Alexander 模型 C^•（R^{(1)} = (A/p)[X] の、A2 の
`polyCosimplicialAlgebra`）から δ 変数つきの D^•（`pdDeltaCechNerve`）への余単体的 A 代数の射、b ↦ φ(b)（X_j^{(i)} ↦ φ(X_j^{(i)})、
z/p ↦ φ(z)/p）。BS 著者版 Theorem 5.2 の証明の η : C^• → D^•。
方針：C^n は B^{n,(1)} ≅ B^n（A 線形な相対 Frobenius b ↦ φ(b)、δ 射）の envelope で、D^n は (A,(p)) 上の prism（Lemma 2.38）かつ
z ∈ J₀ について φ(z) = z^p + pδ(z) = p((p−1)!γ_p(z) + δ(z)) ∈ pD^n なので、A0 の `IsPrismaticEnvelope.lift`。θ との可換は lift の一意性。
規約：A は結晶 prism（生成元 p、hgen）で有界。A = ℤ_p、I = (p) の場合が D68 の `crystallineBridge`（`crystallineBridge_eq_eta`）。
(a) とのつなぎ方：D^• は R′ ≠ R̄ の対象 {D^0/p^e} の Čech 脈体で (a) の枠（全射 k[S] → R̄）の形ではないので、(a) を δ 変数つきの
pro 対象に広げず、δ 変数なしの枠への収縮 `pdDeltaRetraction`（Tot で可逆）を挟む（a1-design §11.3）。
使われ方：`crystallineComparison_polynomial`、`frobeniusPdBridge`。 -/
def etaBridge (P : OrientedPrism p A) (hP : IsBoundedPrism P)
    (hgen : P.generator = p) (γI : DividedPowers I) (hpI : (p : A) ∈ I) (r : ℕ) : polyCosimplicialAlgebra P hP r ⟶ pdDeltaCechNerve p P γI hpI r := by
  sorry -- 各項で相対 Frobenius の δ 射 B^n → D^n を envelope の lift（φ(J₀) ⊆ pD^n、Lemma 2.38 の δ 構造）。余単体的構造は lift の一意性

/-- 概要：δ 変数の収縮 ρ : D_δ^• → D^•（δ 変数つきの D^• から小さい枠 X_j の δ 変数なしの pd Čech 脈体へ、X_j^{(i)} ↦ x_{(j,i)}、
δ^a(X_j^{(i)}) ↦ 0（a ≥ 1））。
方針：B^n → D^n（自由 δ 環を多項式環 A[δ^a(X^{(i)})]^∧ とみて δ^a ↦ 0、a ≥ 1）は J₀ を pd イデアルに送るので pd 包の普遍性で lift。
余単体的構造は lift の一意性。
規約：A1/CrystallineInput の `pdInclusion`（D_0^• → D^•、A = ℤ_p）の左逆：ρ ∘ ι = id。δ 射ではない（δ 構造は使わない）。
site の言葉では pro 対象 {D^0/p^e}（R̄ → R̄）から {D_δ^0/p^e}（R̄ → R′）への site の射の環の側。
使われ方：`pdDeltaRetraction_quasiIso`、`crystallineComparison_polynomial`、`frobeniusPdBridge`。 -/
def pdDeltaRetraction : pdDeltaCechNerve p P γI hpI r ⟶ polyPdCech p γI hpI r := by
  sorry -- 各項で X ↦ x、δ^a(X) ↦ 0（a ≥ 1）を pd 包の普遍性で lift。余単体的構造は lift の一意性

/-- 概要：δ 変数の収縮は交代余面複体の擬同型（G-A1-16 の一般の基底の版。A = ℤ_p では A1/CrystallineInput の `extraCech_comparison`
（包含 ι の側）と同じ）。
方針：D_δ^n ≅ D^n ⊗̂_A E^n（E^• = A[δ^{a}(X_j)]_{a≥1}^{⊗(•+1)} の Čech 余脈体、pd 包は平坦な底変換と可換）で ρ = id ⊗ (高次座標 ↦ 0)。
E^• は増大つきの extra degeneracy（U ↦ 0）で A と余単体的ホモトピー同値、各 mod p^a で収縮し Rlim（Mittag-Leffler）。
規約：A は p 進完備。site を通さない（(a) を δ 変数つきの pro 対象に広げるより軽い、a1-design §11.3）。
使われ方：`crystallineComparison_polynomial`（`totEInfinity_map_isInvertible`）、A1/DeRhamComparisonPoly の `wittSmallBridge_isInvertible`。 -/
theorem pdDeltaRetraction_quasiIso (hk : IsAdicComplete (Ideal.span {(p : A)}) A) :
    QuasiIso ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (pdDeltaRetraction p P γI hpI r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A))) := by
  sorry -- 高次の δ 座標の Čech 因子 E^• の extra degeneracy、D^• とのテンソル、mod p^a ごとの収縮の Rlim

include hgen in
/-- 概要：η から δ 変数を収縮した写像 C^• → D^•（δ 変数なしの小さい枠の pd Čech 脈体）：η ≫ ρ、具体的には X_j^{(i)} ↦ x_{(j,i)}^p
（ρ(φ(X)) = ρ(X^p + pδ(X)) = x^p）。旧 `frobeniusPdBridge`（X ↦ X^p で定義し原典の η と並べていたもの）を、η からの計算として残した。
方針：定義は合成（新しい sorry なし）。
規約：Frobenius との両立は述べない。δ 変数なしの模型（A1/DeRhamComparisonPoly の `pdModel`・`wittBigPdModel`）へつなぐための形。
使われ方：`frobeniusPdBridge_tot`、A1/DeRhamComparisonPoly の `wittSmallBridge`（(A, I) = (W(C), J) のこれと `pdModel_iso_pdCechNerve`）・
`wittBridge_frame_comm`（X ↦ x^p の形）。 -/
def frobeniusPdBridge : polyCosimplicialAlgebra P hP r ⟶ polyPdCech p γI hpI r :=
  etaBridge p P hP hgen γI hpI r ≫ pdDeltaRetraction p P γI hpI r

include hgen in
/-- 概要：Tot の上で、δ 変数なしの枠への写像（`frobeniusPdBridge`）の類は η の類と ρ の類の合成（ρ は Tot で可逆なので、
η と X ↦ X^p の写像は同じ比較を与える）。
方針：`totEInfinity_map` の関手性（nerve の 2 単体 (η, ρ) を `totEInfinityFunctor` で写す）。
規約：ホモトピー圏の等式。
使われ方：A1/DeRhamComparisonPoly の `wittSmallBridge_isInvertible`（(c) を X ↦ X^p の形で読む）。 -/
theorem frobeniusPdBridge_tot :
    HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) A (frobeniusPdBridge p P hP hgen γI hpI r)) =
      HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) A (etaBridge p P hP hgen γI hpI r)) ≫
        HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) A (pdDeltaRetraction p P γI hpI r)) := by
  sorry -- nerve の 2 単体 (η, ρ) の totEInfinityFunctor による像

include hgen in
/-- 概要：**(c)** BS 著者版 Theorem 5.2（I ∋ p の pd イデアル、多項式の場合）：Δ_{R^{(1)}/A} ≃ RΓ_crys(R/A)、R = (A/I)[X_1,…,X_r]。
比較の射は η の Tot（`etaBridge`）、δ 変数の収縮の Tot（`pdDeltaRetraction`）、(a) の同型（`crystallineCechIso`）の逆の合成で、可逆
（BS 著者版 Theorem 5.2 の、多項式の場合。比較写像は原典の η）。
方針：Tot ρ は可逆（`pdDeltaRetraction_quasiIso`・`totEInfinity_map_isInvertible`）なので Tot η の可逆性に帰着。原典の議論：
D_δ^• ≅ C^• ⊗_{B^{•,(1)}} B^•（相対 Frobenius の押し出し、Cor 2.39 の D^n = B^n{φ(J₀)/p}^∧）と Lemma 5.4（A1/CrystallineInput の
`frobeniusTwist_cech_quasiIso_infinite`、k = A/p、変数 Fin r × ℕ）で mod p が cohomology 同型（D68 の段 2 `crystallineBridgeModP_isCohomologyIso` の
一般の基底の版）、両辺 p 完備・p ねじれなしなので導来 Nakayama（G-A1-4）。
一般の I ∋ p は、D_δ^• が (A,(p)) 上の結晶 prism の余単体的対象である（Lemma 2.38）ことから同じ議論が通る
（J̄ ∋ p、mod p で D^n/p = C^n/p ⊗_φ B^n/p は I の pd を加えても成り立つ。紙で確かめる §11.7 の 2）。
規約：A は結晶 prism（生成元 p）で有界、p 進完備。ホモトピー圏の射の可逆性。Frobenius との両立は述べない（E3 で使わない）。
使われ方：A1/DeRhamComparisonPoly の `wittSmallBridge_isInvertible` は (A, I) = (W(C), J) のこれと `frobeniusPdBridge_tot`・Cor 4.12（`psiBaseChange`）
（a1-design §11.3 の段 2）。 -/
theorem crystallineComparison_polynomial (hk : IsAdicComplete (Ideal.span {(p : A)}) A)
    [EssentiallySmall.{u} (CrysOver p γI (crysPolynomial r (I := I)) κ)]
    (hκ : IsCrystallineCutoff A (crysPolynomial r (I := I)) κ) :
    letI := crysResidueAlgebra (J := I) (R := crysPolynomial r (I := I))
    IsIso ((prismaticCohomologyCAlg_eq_totEInfinity (E := E) P hP r).some.hom ≫
      HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) A (etaBridge p P hP hgen γI hpI r)) ≫
      HomotopyCategory.homMk (Cosimplicial.totEInfinity_map (E := E) A (pdDeltaRetraction p P γI hpI r)) ≫
      (crystallineCechIso (E := E) p γI hpI κ (fun j : ULift.{u} (Fin r) => (MvPolynomial.X j.down : crysPolynomial r (I := I)))
        (by sorry) hk hκ (by sorry)).inv) := by -- 枠 X_j は全射、#Fin r ≤ κ
  sorry -- Tot ρ は可逆（pdDeltaRetraction_quasiIso）。押し出し D_δ^• ≅ C^• ⊗_φ B^•、Lemma 5.4（無限変数、k = A/p）、導来 Nakayama（G-A1-4）

end Comparison

/-! ## D68 の `crystallineBridge` との関係 -/

/-- 概要：D68 の `crystallineBridge`（A1/CrystallineInput、(ℤ_p, (p)) の η : C^• → D^•、C^n = B^n{z/p}^∧ → D^n = B^n{φ(z)/p}^∧、b ↦ φ(b)）は
`etaBridge` の (A, I) = (ℤ_p, (p)) の場合：pd 包の同一視 e : `pdDeltaModel p r` ≅ `pdDeltaCechNerve` のもとで二つの η は一致する。
方針：e は `pdDeltaModel` の項 B^n{φ(z)/p}^∧ が J₀ = (p, z) の p 完備な pd 包であること（BS 著者版 Cor 2.39）と pd 包の普遍性。
一致は C^n の envelope の普遍性の一意性（両辺とも相対 Frobenius b ↦ φ(b) の δ 射の lift、φ_{ℤ_p} = id）。
規約：どちらからどちらを得るか：一般の `etaBridge` が本体で、`crystallineBridge` はその特殊化。ただし A1/CrystallineInput は本ファイルより前
（drafts/README の DAG）なので `crystallineBridge` は envelope の lift で独立に定義したままにし、特殊化であることを本補題で述べる。
(p) ⊂ ℤ_p の divided powers は一意（ℤ_p は p ねじれなし）なので γ は変数で受ける。
使われ方：D68 の六段（A1/HodgeTateComparison）と (c)（D69 の A1-5）の比較写像が同じ η であることの記録（design-status §0.3.1、11-07 の決定 3）。 -/
theorem crystallineBridge_eq_eta (γ : DividedPowers (Ideal.span {(p : crystallineBase.{u} p)})) (r : ℕ) :
    ∃ e : pdDeltaModel.{u} p r ≅
        pdDeltaCechNerve p (crystallineBasePrism.{u} p) γ (Ideal.mem_span_singleton_self _) r,
      crystallineBridge p r ≫ Functor.whiskerRight e.hom (Under.forget _) =
        Functor.whiskerRight (etaBridge p (crystallineBasePrism p) (crystallineBaseBounded p) (crystallineBase_generator p)
          γ (Ideal.mem_span_singleton_self _) r) (Under.forget _) := by
  sorry -- e：Cor 2.39 と pd 包の普遍性の一意性。等式：各項で envelope（C^n）の lift の一意性（どちらも b ↦ φ(b)）

end SerrePositivity.BhattScholze.Prismatic
