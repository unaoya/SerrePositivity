-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.Site（仮。BhattScholze/ の下、原典 §4.1）
-- 設計書：formalization-plans/bhatt-scholze/a0-design.md §2.1〜2.4・2.7、単位 A0-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.BhattScholze.Prismatic.PrismOver
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.SetTheory.Cardinal.Arithmetic
-- 本ファイルは drafts/Sheaves/{SheafCondition,GlobalSections}.lean と drafts/DerivedGeneral/ScalarRestriction.lean（M13）を使う。

/-!
# prismatic site とその構造層（BS 著者版 Def 4.1、Rem 4.6、Not 4.16）

## 概要
向き付き有界 prism (A, (d)) と p 完備な A/d 代数 R について、原典 Def 4.1 の prismatic site (R/A)_Δ を定義する：
対象は (A,(d)) 上の有界 prism (B, dB) と R → B/dB の組、被覆は忠実平坦な prism の射、構造層 O_Δ(B) = B、Ō_Δ(B) = B/dB。
Not 4.16 の Δ_{R/A} := RΓ((R/A)_Δ, O_Δ) を、∞ 層の層 Sheaves の `derivedGlobalSections` で定義する。
Rem 4.6 の完全 prismatic site と、O_Δ の Frobenius（Construction 7.6 が使う）も定義する。

## 方針
環の側の圏 `PrismOver`（prism の射で、R からの写像と両立するもの）を作り、site はその opposite（原典 Cor 3.12 の「prism の圏の opposite」）。
平坦位相は忠実平坦な射の篩が生成する最小の Grothendieck 位相（Mathlib の完備束の `sInf`）。site の公理（Cor 3.12 前半）は
「被覆篩は忠実平坦な射で refine できる」という定理として別に入れる（設計書 D22）。大きい site は濃度 ≤ κ で切り落とし
（ノート D16、κ = (#A + #R + ℵ₀)^{ℵ₀}）、本質的に小さいことを定理にして Mathlib の `SmallModel` を site にする。

## 規約
基底は向き付き（ノート D5）で有界（既存の形：A/d の p 冪ねじれが一様な冪で消える）。R に smooth 性は仮定しない（定義は任意の
p 完備 A/d 代数について、定理は多項式代数について）。RΓ は Čech 層の層化と大域切断（ノート D17：古典的 RΓ との差は離散な層では消える）。
値はまず D(A)（`derivedInfinityCategory A`）。CAlg 値は A2・A4。

## 使われ方
Constr 4.17・4.18（Čech–Alexander 複体、`drafts/A0/CechAlexander.lean`）、Cor 3.12・Lemma 3.7(2)(3)（`drafts/A0/FlatDescent.lean`）、A1 の Thm 4.11 の定式化、
A5 の Prop 8.5（完全 site）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial Cardinal

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime]

variable {A : Type u} [CommRing A] (P : OrientedPrism p A) (hP : IsBoundedPrism P)
variable (R : Type u) [CommRing R] [Algebra (A ⧸ P.ideal) R]

namespace PrismOver

variable {P R} {κ : Cardinal.{u}}

/-- 概要：射が忠実平坦：B → C が (p, d) 完全忠実平坦（原典の「(p, IB) 完全忠実平坦」）。
方針：共通基盤の `IsCompletelyFaithfullyFlat`（イデアル (p, d)、C を B 加群として）。
規約：Lemma 3.7(3) により、これが原典の「忠実平坦な prism の射」。
使われ方：平坦位相の生成系、Cor 3.12。 -/
def IsFaithfullyFlat {X Y : PrismOver P R κ} (f : X ⟶ Y) : Prop :=
  letI : Algebra X.B Y.B := f.toHom.toRingHom.toAlgebra
  IsCompletelyFaithfullyFlat (Ideal.span {(p : X.B), X.Q.generator}) Y.B

/-- 概要：濃度 ≤ κ の prism の圏は本質的に小さい。
方針：各対象は、濃度 κ の固定した型の部分型を台とする対象と同型（環・δ・prism・射の構造を全単射で移す）。
規約：κ ≥ #A + #R が要る。
使われ方：site を小さい圏（`SmallModel`）にする。 -/
theorem essentiallySmall (hκ : Cardinal.mk A + Cardinal.mk R ≤ κ) :
    EssentiallySmall.{u} (PrismOver P R κ) := by
  sorry -- 構造の全単射による移送（a0-design §2.7）

end PrismOver

/-! ## site・位相・構造層（Def 4.1） -/

variable (κ : Cardinal.{u}) [EssentiallySmall.{u} (PrismOver P R κ)]

/-- 概要：(R/A)_Δ の小さい模型（環の側）。
方針：Mathlib の `SmallModel` と `equivSmallModel`。
規約：以後の site・前層はこの小さい圏の上で述べ、大きい圏との比較は `equivSmallModel` で。
使われ方：∞ 層の層 Sheaves は小さい圏を仮定する。 -/
abbrev PrismOverSmall : Type u := SmallModel (PrismOver P R κ)

/-- 概要：prismatic site (R/A)_Δ：prism の圏の opposite（原典 Def 4.1・Cor 3.12）。
方針：`PrismOverSmall` の opposite。
規約：被覆は忠実平坦な射（環の側の射の opposite）。
使われ方：平坦位相、構造層、Δ_{R/A}。 -/
abbrev PrismaticSite : Type u := (PrismOverSmall P R κ)ᵒᵖ

/-- 概要：小さい模型の射が忠実平坦：`equivSmallModel` で大きい圏へ送った射が忠実平坦。
方針：性質の移送。
規約：同値に沿うので well-defined。
使われ方：平坦位相の生成系。 -/
def PrismOverSmall.IsFaithfullyFlat {X Y : PrismOverSmall P R κ} (f : X ⟶ Y) : Prop :=
  PrismOver.IsFaithfullyFlat ((equivSmallModel (PrismOver P R κ)).inverse.map f)

/-- 概要：平坦位相：忠実平坦な射 f : B → C の篩（site では f.op : C → B で生成される篩）を被覆に含む最小の Grothendieck 位相。
方針：`GrothendieckTopology` の完備束の `sInf`。site の公理の検証は不要。
規約：原典 Def 4.1 の「flat cover」。Cor 3.12 前半（押し出しの存在）は `flatTopology_refine` に。
使われ方：Δ_{R/A} の RΓ の位相。 -/
def flatTopology : GrothendieckTopology (PrismaticSite P R κ) :=
  sInf { J | ∀ {X Y : PrismOverSmall P R κ} (f : X ⟶ Y), PrismOverSmall.IsFaithfullyFlat P R κ f →
    Sieve.generate (Presieve.singleton f.op) ∈ J (Opposite.op X) }
-- W9-I-10：f : X → Y（環 B_X → B_Y）の opposite f.op : op Y → op X が生成する篩は op X 上（被覆先は Spf(B_X)）。

/-- 概要：Cor 3.12 前半：平坦位相の被覆篩は、忠実平坦な**単一の射**の篩で refine できる（忠実平坦な射の押し出しが存在し忠実平坦）。
方針：押し出しは完備テンソル (B′ ⊗̂^L_B C)^∧ で、Lemma 3.7(2) により有界 prism、B′ 上忠実平坦。κ は `IsAdmissibleCutoff`（押し出しが切り落としに残る、W9-I-11）。
規約：D22。この定理により忠実平坦な単一射の族は Mathlib の `Coverage` をなし、`flatTopology` はその `toGrothendieck`。被覆先 U を固定し、単一射の presieve は U 上（W9-I-10）。
使われ方：層条件を生成系（忠実平坦な単一射）で確かめてよいこと（S1 の `isSheaf_toGrothendieck_iff`）。 -/
theorem flatTopology_refine (hκ : IsAdmissibleCutoff P R κ) :
    ∃ K : Coverage (PrismaticSite P R κ), K.toGrothendieck = flatTopology P R κ ∧
      ∀ {U : PrismaticSite P R κ} (Rp : Presieve U), Rp ∈ K.covering U →
        ∃ (Y : PrismOverSmall P R κ) (f : U.unop ⟶ Y), PrismOverSmall.IsFaithfullyFlat P R κ f ∧
          Rp = Presieve.singleton f.op := by
  sorry -- A0-3d（Cor 3.12 (a)）。FlatDescent の PrismOver.exists_isPushout_isFaithfullyFlat・isFaithfullyFlat_of_isIso・
        -- IsFaithfullyFlat.comp から（中身の段階で FlatDescent の後へ移す）

/-- 概要：構造層 O_Δ：B ↦ B（環の前層。site の前層 (PrismaticSite)ᵒᵖ ⥤ CommRingCat は PrismOverSmall ⥤ CommRingCat）。
方針：小さい模型から `equivSmallModel.inverse` で大きい圏へ送り、台の環を取る。
規約：A 代数の構造は `toHom` から（CommRingCat の値は環だけ）。
使われ方：Δ_{R/A}。 -/
def structurePresheaf : PrismOverSmall P R κ ⥤ CommRingCat.{u} :=
  (equivSmallModel (PrismOver P R κ)).inverse ⋙
    { obj := fun X => CommRingCat.of X.B
      map := fun f => CommRingCat.ofHom f.toHom.toRingHom
      map_id := by sorry
      map_comp := by sorry }

/-- 概要：被約構造層 Ō_Δ：B ↦ B/dB。
方針：剛性により dB = Q.ideal。
規約：A/d 代数の前層だが、ここでは環の前層として。
使われ方：Ō_{R/A} との比較（Cor 3.12 の最後の文）。 -/
def reducedStructurePresheaf : PrismOverSmall P R κ ⥤ CommRingCat.{u} :=
  (equivSmallModel (PrismOver P R κ)).inverse ⋙
    { obj := fun X => CommRingCat.of (X.B ⧸ X.Q.ideal)
      map := fun f => CommRingCat.ofHom f.toHom.quotientMap
      map_id := by sorry
      map_comp := by sorry }

/-- 概要：O_Δ の Frobenius：各 B の δ 構造の φ_B（環の自然変換。A 上は φ_A 半線形）。
方針：δ 射は φ と可換するので自然。
規約：A 代数の射ではない（半線形）。D(A) では φ_A に沿うスカラー制限を付けて述べる。
使われ方：Δ_{R/A} の Frobenius、Construction 7.6、Def 8.2 の Frobenius 余極限。 -/
def structurePresheafFrobenius : structurePresheaf P R κ ⟶ structurePresheaf P R κ where
  app X := CommRingCat.ofHom (((equivSmallModel (PrismOver P R κ)).inverse.obj X).Q.deltaStructure.frobeniusLift)
  naturality := by sorry -- δ 射は Frobenius 持ち上げと可換（`isDeltaHom_frobeniusLift_general` の系）

/-! ## 完全 prismatic site（Rem 4.6） -/

/-- 概要：完全 prismatic site：B が完全（φ_B 全単射）な対象の充満部分圏（の opposite）。
方針：`ObjectProperty.FullSubcategory`。
規約：Thm 3.10 により perfectoid 環 B/dB の圏と同値（定理、A5）。
使われ方：Lemma 8.4、Prop 8.5（E3 の `limitCone`）。 -/
def PerfectPrismaticSite : Type u :=
  (ObjectProperty.FullSubcategory (fun X : PrismOverSmall P R κ =>
    Function.Bijective ((equivSmallModel (PrismOver P R κ)).inverse.obj X).Q.deltaStructure.frobeniusLift))ᵒᵖ

/-! ## Δ_{R/A}（Not 4.16） -/

/-- 概要：O_Δ を D(A) 値前層として読む：B を A 代数（`toHom`）とみなし、離散埋め込み `discreteEmbedding A` で D(A) へ。
方針：`PrismOver P R κ ⥤ Under (CommRingCat.of A)` の nerve を `discreteEmbedding` に前合成し、小さい模型の形状
（`presheafShape (PrismaticSite)`、すなわち `uliftFunctor.obj (nerve (PrismOverSmall))`）から大きい nerve への射で引き戻す。
規約：E3 の `J R = discreteEmbedding R` と同じ埋め込み。
使われ方：Δ_{R/A} の RΓ の入力。
小さい模型の比較は Core/SmallModelNerve の `smallModelNerveComparison`（IF-G1 Core、main 7bda72c3c）。 -/
def structurePresheafDerived :
    InfinityCategories.Sheaves.Presheaf (PrismaticSite P R κ) (InfinityCategories.derivedInfinityCategory A) :=
  sorry -- 小さい模型の持ち上げた nerve → nerve (PrismOver) → nerve (Under A) → D(A)

/-- 概要：Not 4.16：Δ_{R/A} := RΓ((R/A)_Δ, O_Δ)。
方針：∞ 層の層 Sheaves の `derivedGlobalSections`（層化してから大域切断）。層化のデータと D(A) の presentable 性は入力（S4・G3）。
規約：値は選んだ極限錐の頂点。使う側は普遍性（`prismaticCohomologyCone`）で扱う。Čech 層の RΓ（D17）。
使われ方：Constr 4.18、Lemma 4.20、A1 の Thm 4.11、A2 の Construction 7.6。 -/
def prismaticCohomology
    (hJ : InfinityCategories.Sheaves.Sheafification (flatTopology P R κ) (InfinityCategories.derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (InfinityCategories.derivedInfinityCategory A)) :
    (InfinityCategories.derivedInfinityCategory A) _⦋0⦌ :=
  InfinityCategories.Sheaves.derivedGlobalSections (flatTopology P R κ) hJ hE (structurePresheafDerived P R κ)

/-- 概要：Not 4.16：Ō_{R/A} := Δ_{R/A} ⊗^L_A A/d。
方針：D(A) のテンソル（基盤の完備テンソル／Koszul の形）。
規約：Ō_Δ の RΓ との一致は定理（Cor 3.12 の最後の文、A/d は完全複体）。
使われ方：A1 の HT 比較の対象。
要確認：D(A) の A/d とのテンソルを与える基盤の名前。 -/
def hodgeTateCohomology
    (hJ : InfinityCategories.Sheaves.Sheafification (flatTopology P R κ) (InfinityCategories.derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (InfinityCategories.derivedInfinityCategory A)) :
    (InfinityCategories.derivedInfinityCategory A) _⦋0⦌ :=
  sorry -- prismaticCohomology ⊗^L_A A/d（`tensorWith`、FlatDescent の `reducedStructurePresheafDerived` と同じ A/d の頂点）

/-- 概要：Δ_{R/A} の Frobenius：Δ → φ_{A*}Δ。
方針：`structurePresheafFrobenius` を D(A) 値前層の射にし、`derivedGlobalSections_map`。半線形性は φ_A に沿うスカラー制限で。
規約：D(A) の辺。
使われ方：A2 の多項式上の Frobenius、A4 の正の反復（Def 8.2）。 -/
def prismaticCohomologyFrobenius
    (hJ : InfinityCategories.Sheaves.Sheafification (flatTopology P R κ) (InfinityCategories.derivedInfinityCategory A))
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (InfinityCategories.derivedInfinityCategory A)) :
    let Δ := prismaticCohomology P R κ hJ hE
    let res := InfinityCategories.derivedInfinityRestrictScalars P.deltaStructure.frobeniusLift
    SSet.Edge Δ (res.app (Opposite.op ⦋0⦌) Δ) := by
  sorry -- 各 B の Frobenius は B → Res_φ B として A 線形。S2 で誘導した辺の標的を極限保存で Res_φ Δ に移す

/-- 濃度の上限だけを緩める環側の包含。射の二つの可換条件も同じものを使う。 -/
def prismOverCutoffInclusion {κ κ' : Cardinal.{u}} (hle : κ ≤ κ') :
    PrismOver P R κ ⥤ PrismOver P R κ' where
  obj X := { B := X.B, ring := X.ring, Q := X.Q, bounded := X.bounded,
             toHom := X.toHom, sec := X.sec, sec_comp := X.sec_comp, small := X.small.trans hle }
  map f := ⟨f.toHom, f.comm_base, f.comm_sec⟩
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

/-- 小さい模型に移した site 側の包含。 -/
def cutoffSiteInclusion {κ κ' : Cardinal.{u}} [EssentiallySmall.{u} (PrismOver P R κ)]
    [EssentiallySmall.{u} (PrismOver P R κ')] (hle : κ ≤ κ') :
    PrismaticSite P R κ ⥤ PrismaticSite P R κ' :=
  ((equivSmallModel (PrismOver P R κ)).inverse ⋙ prismOverCutoffInclusion P R hle ⋙
    (equivSmallModel (PrismOver P R κ')).functor).op

/-- 大きい cutoff の構造前層を包含の opposite に沿って制限する。 -/
def restrictCutoffStructure {κ κ' : Cardinal.{u}} [EssentiallySmall.{u} (PrismOver P R κ)]
    [EssentiallySmall.{u} (PrismOver P R κ')] (hle : κ ≤ κ') :
    InfinityCategories.Sheaves.Presheaf (PrismaticSite P R κ) (InfinityCategories.derivedInfinityCategory A) :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cutoffSiteInclusion P R hle).op) ≫
    structurePresheafDerived P R κ'

-- HasEnvelopes を仮定する prismaticCohomology_cutoff_invariant は
-- CechAlexander.lean の prismaticCohomology_eq_cechAlexanderTot の直後に置く。

end SerrePositivity.BhattScholze.Prismatic
