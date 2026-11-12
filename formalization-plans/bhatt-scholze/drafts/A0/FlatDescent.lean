-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.FlatDescent（仮。原典 §3 Lemma 3.7(2)(3)・Cor 3.12）
-- 一般の D(A) の述語 `IsCompletelyFlatObject` は SerrePositivity.InfinityCategories.Derived（M13 の隣）へ移す候補。
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.6、単位 A0-3b・A0-3d。基準コミット b2ef94226。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.BaseChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Homology
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.Fixed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Sheaf
-- 本ファイルは drafts/A0/PrismaticSite.lean（site・O_Δ・Δ_{R/A}）、drafts/DerivedGeneral/{Truncation,CompletionFunctor}.lean
-- （`IsConnectiveAt`・`IsCoconnectiveAt`・`discreteModuleEmbedding`・`IsDerivedComplete`）、drafts/Sheaves/{SheafCondition,GlobalSections}.lean を import する。

/-!
# 有界 prism 上の完全平坦な複体と、prism の site（BS 著者版 Lemma 3.7(2)(3)、Cor 3.12）

## 概要
Lemma 3.7(2)：有界 prism (A,(d)) 上の (p,d) 完全平坦な複体 M ∈ D(A)（導来 (p,d) 完備）は離散で古典的に (p,d) 完備、
M[dⁿ] = 0、M/dⁿM の p 冪ねじれは有界。Lemma 3.7(3)：(p,d) 完全平坦な δ-A 代数 B について (B, dB) は有界 prism で、
A → B は prism の射（原典の「平坦な prism の射の圏 ＝ 完全平坦な δ-A 代数の圏」の対象の部分）。
Cor 3.12：固定基底 (A,(d)) 上の site (R/A)_Δ について、(a) 忠実平坦な射は同型・合成・押し出しで閉じ（site の公理）、
(b) O_Δ（B ↦ B）と Ō_Δ（B ↦ B/dB）は平坦位相の（1 圏の）層、(c)(d) D(A) 値の O_Δ は忠実平坦な単一射に沿って降下し
∞ 層（高次コホモロジーの消滅の導来の意味）、(e) したがって Δ_{R/A} = RΓ(O_Δ) は O_Δ 自身の極限。

## 方針
Lemma 3.7(2) は原典の証明：M ⊗^L A/dⁿ は有界 p 冪ねじれの A/dⁿ 上の p 完全平坦な複体なので [BMS19, Lemma 4.7] で離散、
導来 d 完備性で M 自身も離散、古典的完備性は (1)（本体 `boundedPrism_pair_isAdicComplete`）と同じ計算。
Lemma 3.7(3) は (2) で B[d] = 0 と B/dB の有界性を得て、`OrientedPrism.ofDistinguished`（d の像は distinguished のまま）。
Cor 3.12 (a) の押し出しは完備テンソル (B′ ⊗^L_B C)^∧ と Lemma 3.7(2)。(c) は原典の証明：mod (pⁿ, dⁿ) で
忠実平坦な Amitsur 複体の完全性（底変換後の収縮ホモトピー）を示し、Koszul 塔の逆極限（Milnor 列）で D(A) の極限錐にする
（HA/CompleteFaithfullyFlatDescent はスカラー同種写像の降下だけで再利用できない、a0-design §2.6）。(d) は (c) と
S1 の `isSheaf_toGrothendieck_iff`（`flatTopology_refine` の被覆族で）。Ō_Δ の D(A) 値は O_Δ と A/d の導来テンソルで
（原典の「tensoring」）、d が各 B で正則なので値は B/dB。

## 規約
基底は向き付き有界（ノート D5・D19）。「(p,d) 完全平坦な複体」は原典 §1.2 の定義（d 冪・p 冪ねじれの任意の加群 N について
M ⊗^L_A N が次数 0 に集中）を `tensorWith` で書く。Lemma 3.7(2) の「M」は導来 (p,d) 完備とする（原典の証明が使う仮定。
Lemma 3.7 の直後の注意も「derived (p,I)-complete (p,I)-completely flat」の圏について述べる）。Cor 3.12 は全 prism の site
ではなく、固定基底 (A,(d)) 上の site (R/A)_Δ について述べる（原典の一般形ではなく、Def 4.1 の site の場合。E3 に要るのはこれだけ）。
(e) の「古典的な RΓ との一致」（hypersheaf、ノート D17）は述べない：Δ_{R/A} は Čech 層の RΓ で定義する（D17）。

## 使われ方
`flatTopology_refine`（PrismaticSite、Cor 3.12 (a) の押し出しから。中身の段階で本ファイルへ移すか、本ファイルを先に置く）、
`prismaticCohomology_eq_cechAlexanderTot`（CechAlexander、(d)(e)）、Prop 3.13(1)（PrismaticEnvelope。自由加群の場合は直接）、
A2 の `prismaticCohomologyCAlg`（(d) の CAlg 版）、A5 の G-A5-5（完全 site への制限）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

/-! ## D(A) の対象の完全平坦性（原典 §1.2） -/

namespace SerrePositivity.InfinityCategories.Derived

/-- 概要：M ∈ D(A) が I 完全平坦：I 冪ねじれの任意の A 加群 N について M ⊗^L_A N が次数 0 に集中する（原典 §1.2）。
方針：N を `discreteModuleEmbedding` で D(A) に入れ、∞ 関手 `tensorWith M` の値の H^i（i ≠ 0）の消滅で書く。
規約：「I 冪ねじれ」は各元が I の或る冪で消えること。加群の版は本体の `IsCompletelyFlat`（Tor の消滅）で、
離散な M ではこれと一致する（中身の段階で比較の補題を置く）。cohomological な添字（`IsConnectiveAt 0 ∧ IsCoconnectiveAt 0`）。
使われ方：Lemma 3.7(2)、Cor 3.12 (a) の押し出しの平坦性。 -/
def IsCompletelyFlatObject {A : Type u} [CommRing A] (I : Ideal A) (M : (derivedInfinityCategory A) _⦋0⦌) : Prop :=
  ∀ N : ModuleCat.{u} A, (∀ x : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0) →
    let Y := (tensorWith M).app _ ((discreteModuleEmbedding A).app _ (nerveVertex N))
    IsConnectiveAt A 0 Y ∧ IsCoconnectiveAt A 0 Y

end SerrePositivity.InfinityCategories.Derived

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion SerrePositivity.InfinityCategories


variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-! ## Lemma 3.7(2)(3) -/

/-- 概要：Lemma 3.7(2)：有界 prism (A,(d)) 上の導来 (p,d) 完備で (p,d) 完全平坦な M ∈ D(A) は離散（H^i = 0、i ≠ 0）で、
H⁰(M) は古典的に (p,d) 完備、dⁿ ねじれがなく、H⁰(M)/dⁿ の p 冪ねじれは有界。
方針：原典の証明。M ⊗^L A/dⁿ ≃ M/dⁿM が離散で有界 p 冪ねじれ（[BMS19, Lemma 4.7]、A/dⁿ の有界性は A/d の有界性の d 進 dévissage）、
導来 d 完備性で M も離散。古典的完備性は (1) の Koszul 塔の計算（本体 `boundedPrism_pair_isAdicComplete` と同じ）。
自由加群の完備化の場合は a0-design §5.1 の 1 で検証済み。
規約：原典の一般形（基底は向き付き、D19）。導来完備性は仮定（§規約）。
使われ方：Cor 3.12 (a)（押し出しが有界 prism）、Lemma 3.7(3)、Prop 3.13(1)。 -/
open Classical in
theorem isDiscrete_of_completelyFlat_boundedPrism (hP : IsBoundedPrism P)
    (M : (derivedInfinityCategory A) _⦋0⦌)
    (hc : Derived.IsDerivedComplete A {(p : A), P.generator} M)
    (hM : Derived.IsCompletelyFlatObject (Ideal.span {(p : A), P.generator}) M) :
    let H := derivedInfinityHomology A 0 M
    Derived.IsConnectiveAt A 0 M ∧ Derived.IsCoconnectiveAt A 0 M ∧
      IsAdicComplete (Ideal.span {(p : A), P.generator}) H ∧
      (∀ (n : ℕ) (x : H), P.generator ^ n • x = 0 → x = 0) ∧
      ∀ n : ℕ, ∃ N : ℕ, ∀ (k : ℕ) (x : H ⧸ (Ideal.span {P.generator ^ n} • ⊤ : Submodule A H)),
        (p : A) ^ k • x = 0 → (p : A) ^ N • x = 0 := by
  sorry -- A0-3b。M ⊗^L A/dⁿ の離散性（BMS19 4.7）→ 導来 d 完備性で離散 → (1) と同じ塔の計算

/-- 概要：Lemma 3.7(3)：(p,d) 完全平坦で導来 (p,d) 完備な δ-A 代数 B について、(B, dB) は有界な向き付き prism で、
A → B は prism の射（原典の「(忠実) 平坦な prism の射の圏 ＝ (p,I) 完全 (忠実) 平坦な δ-A 代数の圏」の対象の対応）。
方針：(2) を B に当てて B[d] = 0 と B/dB の有界 p 冪ねじれ、δ 射は distinguished 元を distinguished 元に送るので
`OrientedPrism.ofDistinguished`。逆向き（平坦な prism の射 (A,(d)) → (B,J) では J = dB）は剛性 `OrientedPrism.Hom.map_ideal_eq`。
規約：原典の一般形のうち対象の対応を主張にする（射の対応は δ-A 射そのものなので自明）。忠実平坦の場合は同じ構成で
`PrismOver.IsFaithfullyFlat` が定義どおり成り立つ（原典 Def 3.2(3) の flat の定義は (p,I) 完全平坦）。
使われ方：Cor 3.12 (a)（押し出しを prism にする）、A5 の完全化の被覆。 -/
theorem exists_boundedPrism_of_completelyFlat (hP : IsBoundedPrism P)
    {B : Type u} [CommRing B] (δB : DeltaStructure p B) (f : A →+* B)
    (hf : P.deltaStructure.IsDeltaHom δB f)
    (hBp : IsModuleComplete B (p : B) (ModuleCat.of B B))
    (hBd : IsModuleComplete B (f P.generator) (ModuleCat.of B B))
    (hflat : letI := f.toAlgebra; IsCompletelyFlat (Ideal.span {(p : A), P.generator}) B) :
    ∃ (Q : OrientedPrism p B) (g : OrientedPrism.Hom P Q),
      Q.deltaStructure = δB ∧ Q.generator = f P.generator ∧ g.toRingHom = f ∧ IsBoundedPrism Q := by
  sorry -- A0-3b。B を離散な D(A) の対象として isDiscrete_of_completelyFlat_boundedPrism、ofDistinguished

/-! ## Cor 3.12 (a)：site の公理（固定基底の site で） -/

variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

namespace PrismOver

variable {P R} {κ : Cardinal.{u}}

/-- 概要：Cor 3.12 (a) の一：同型は忠実平坦（被覆）。
方針：環同型は (p,d) 完全忠実平坦。
規約：原典の「automatic」。
使われ方：`flatTopology_refine` の被覆族が `Coverage` をなすこと。 -/
theorem isFaithfullyFlat_of_isIso {X Y : PrismOver P R κ} (f : X ⟶ Y) [IsIso f] : IsFaithfullyFlat f := by
  sorry -- 環同型に沿う加群は自由で階数 1

/-- 概要：Cor 3.12 (a) の二：忠実平坦な射の合成は忠実平坦。
方針：完全忠実平坦性の合成（mod (p,d) の忠実平坦性の合成と、Tor の消滅の推移）。
規約：原典の「automatic」。
使われ方：同上。 -/
theorem IsFaithfullyFlat.comp {X Y Z : PrismOver P R κ} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsFaithfullyFlat f) (hg : IsFaithfullyFlat g) : IsFaithfullyFlat (f ≫ g) := by
  sorry -- mod (p,d) の忠実平坦の合成と、完全平坦性の推移（derivedTensor の結合）

/-- 概要：Cor 3.12 (a) の三：忠実平坦な f : X → Y と任意の g : X → X′ について、押し出し Y′ が (R/A)_Δ（環の側）に存在し、
X′ → Y′ は忠実平坦。
方針：Y′ := (B_{X′} ⊗^L_{B_X} B_Y)^∧（導来 (p,d) 完備化）。B_{X′} 上 (p,d) 完全忠実平坦なので、`exists_boundedPrism_of_completelyFlat`
（Lemma 3.7(2)(3)）で離散な有界 prism。R → B_{Y′}/d は X′ から。押し出しの普遍性は完備テンソルの普遍性。濃度は ≤ κ^{ℵ₀} = κ。
規約：κ は `IsAdmissibleCutoff`（W9-I-11）。固定基底の site の場合（原典は全有界 prism の圏）。
使われ方：`flatTopology_refine`、(c) の Čech 脈体の項（完備テンソル冪）。 -/
theorem exists_isPushout_isFaithfullyFlat (hκ : IsAdmissibleCutoff P R κ)
    {X Y X' : PrismOver P R κ} (f : X ⟶ Y) (hf : IsFaithfullyFlat f) (g : X ⟶ X') :
    ∃ (Y' : PrismOver P R κ) (f' : X' ⟶ Y') (g' : Y ⟶ Y'), IsPushout f g g' f' ∧ IsFaithfullyFlat f' := by
  sorry -- A0-3d。完備テンソル（HA/DerivedCompletion の CompletedBaseChange*、BS/Perfectoidization/CompletedTensor）と
        -- exists_boundedPrism_of_completelyFlat。普遍性は δ 構造の完備テンソルへの延長の一意性

end PrismOver

/-! ## Cor 3.12 (b)〜(e)：O_Δ と Ō_Δ は層で、高次コホモロジーが消える -/

variable (κ : Cardinal.{u}) [EssentiallySmall.{u} (PrismOver P R κ)]

/-- 概要：Cor 3.12 (b)：O_Δ（B ↦ B）は平坦位相の 1 圏の層（環に値をとる）。
方針：忠実平坦な B → C について B → C ⇉ C ⊗̂_B C が等化子（(c) の H⁰、または mod (pⁿ,dⁿ) の Amitsur と逆極限）。
規約：site の前層は `unopUnop _ ⋙ structurePresheaf`（PrismaticSite の opposite は PrismOverSmall の二重 opposite）。
使われ方：A5・A6 の 1 圏の議論（完全 site への制限）、(d) の H⁰。 -/
theorem structurePresheaf_isSheaf (hκ : IsAdmissibleCutoff P R κ) :
    Presheaf.IsSheaf (flatTopology P R κ) (unopUnop _ ⋙ structurePresheaf P R κ) := by
  sorry -- A0-3d。flatTopology_refine で単一射の篩に帰着し、structurePresheafDerived_isLimit_singleton の H⁰

/-- 概要：Cor 3.12 (b) の Ō_Δ 版：B ↦ B/dB は平坦位相の 1 圏の層。
方針：(b) の等化子列に A/d を掛ける（各項で d 正則、Lemma 3.7(2)）。
規約：同上。
使われ方：A1 の HT 側の比較（Ō の H⁰）。 -/
theorem reducedStructurePresheaf_isSheaf (hκ : IsAdmissibleCutoff P R κ) :
    Presheaf.IsSheaf (flatTopology P R κ) (unopUnop _ ⋙ reducedStructurePresheaf P R κ) := by
  sorry -- A0-3d。(c) の極限錐に A/d を導来テンソル（有限 Koszul なので極限と交換）し H⁰ を取る

/-- 概要：Cor 3.12 (c)：忠実平坦な単一射 f : X → Y（site では f.op : Y → X）の生成する篩で、D(A) 値の O_Δ は降下する
（制限錐が極限錐。導来の意味の「高次 Čech コホモロジーの消滅」）。
方針：原典の証明。篩の制限図式の極限は f の Čech 脈体（完備テンソル冪 Y^{⊗̂(n+1)}、(a) の押し出し）の Tot で、
Kos(B_X; pⁿ, dⁿ) → Kos(B_Y^{⊗̂•}; pⁿ, dⁿ) は単体的可換環の忠実平坦降下で極限図式（Amitsur 複体の完全性、底変換後の
収縮ホモトピー）、n について逆極限（Milnor 列）。a0-design §5 の 5・6 の紙の検証が先。
規約：D(A) 値の O_Δ は `structurePresheafDerived`。錐は S1 の `restrictionCone`。
使われ方：(d)。 -/
theorem structurePresheafDerived_isLimit_singleton (hκ : IsAdmissibleCutoff P R κ)
    {X Y : PrismOverSmall P R κ} (f : X ⟶ Y) (hf : PrismOverSmall.IsFaithfullyFlat P R κ f) :
    IsLimitCone (restrictionCone (structurePresheafDerived P R κ)
      (Sieve.generate (Presieve.singleton f.op))) := by
  sorry -- A0-3d。篩の制限図式から f の Čech 脈体への余終性（S3 の型）、有限段の Amitsur と Milnor 列

/-- 概要：Cor 3.12 (d)：D(A) 値の O_Δ は平坦位相の ∞ 層。
方針：`flatTopology_refine` の被覆族（忠実平坦な単一射）で S1 の `isSheaf_toGrothendieck_iff` に帰着し、(c)。
規約：Čech 層（ノート D17）。
使われ方：`prismaticCohomology_isLimit`、`prismaticCohomology_eq_cechAlexanderTot`、A2（CAlg 版は `isSheaf_iff_forget`）。 -/
theorem structurePresheafDerived_isSheaf (hκ : IsAdmissibleCutoff P R κ) :
    Sheaves.IsSheaf (flatTopology P R κ) (structurePresheafDerived P R κ) := by
  sorry -- flatTopology_refine と isSheaf_toGrothendieck_iff、structurePresheafDerived_isLimit_singleton

/-- 概要：Ō_Δ を D(A) 値前層として：O_Δ と A/d の導来テンソル（原典の「tensoring」）。値は B ⊗^L_A A/d ≃ B/dB（d は B で正則）。
方針：`structurePresheafDerived` に ∞ 関手 `tensorWith (A/d)` を後合成する（A/d は `discreteModuleEmbedding` の像）。
規約：新しい前層の定義を足さず、既存の O_Δ と基盤の ⊗^L で書く。B/dB との一致は定理（中身の段階）。
使われ方：(d) の Ō 版、Not 4.16 の Ō_{R/A}（`hodgeTateCohomology`）との比較。 -/
abbrev reducedStructurePresheafDerived :
    Sheaves.Presheaf (PrismaticSite P R κ) (derivedInfinityCategory A) :=
  structurePresheafDerived P R κ ≫
    tensorWith ((Derived.discreteModuleEmbedding A).app _ (nerveVertex (ModuleCat.of A (A ⧸ P.ideal))))

/-- 概要：Cor 3.12 (d) の Ō_Δ 版：D(A) 値の Ō_Δ は平坦位相の ∞ 層。
方針：A/d は完全複体（Kos(A; d)、d 正則）なので `tensorWith (A/d)` は極限錐を保つ（有限極限＝cofiber で書ける）。(d) から。
規約：Čech 層。
使われ方：Ō_{R/A} = RΓ(Ō_Δ)（Cor 3.12 の最後の文）、A1 の `cechAlexanderReducedComplex` の根拠。 -/
theorem reducedStructurePresheafDerived_isSheaf (hκ : IsAdmissibleCutoff P R κ) :
    Sheaves.IsSheaf (flatTopology P R κ) (reducedStructurePresheafDerived P R κ) := by
  sorry -- structurePresheafDerived_isSheaf と、A/d との ⊗^L が完全関手で極限錐を保つこと

/-- 概要：Cor 3.12 (e)：「高次コホモロジーが消える」：Δ_{R/A} = RΓ((R/A)_Δ, O_Δ) は O_Δ 自身の極限錐の頂点。
方針：(d) と S2 の `derivedGlobalSections_of_isSheaf`。
規約：Čech 層の RΓ（D17）。古典的な層コホモロジーとの一致（hypersheaf）は述べない。
使われ方：`prismaticCohomology_eq_cechAlexanderTot`（CechAlexander）。 -/
theorem prismaticCohomology_isLimit (hκ : IsAdmissibleCutoff P R κ)
    (hJ : Sheafification (flatTopology P R κ) (derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (derivedInfinityCategory A)) :
    ∃ c : JoinCone (structurePresheafDerived P R κ),
      IsLimitCone c ∧ c.vertex = prismaticCohomology P R κ hJ hE :=
  derivedGlobalSections_of_isSheaf (flatTopology P R κ) hJ hE (structurePresheafDerived_isSheaf P R κ hκ)

end SerrePositivity.BhattScholze.Prismatic
