# BS-M15（⑤d）作業報告 — M10 着手前の接続と B4（§6〜§13、2026-11-14）

元の報告：[report-codex-m15.md](../../bhatt-scholze/reports/report-codex-m15.md)

## 6. M10 の厳密な相対圏の族への接続（11-14、着手前）

main の `fb3dfd20e` までの文書（共通の /goal・一覧の進捗規則）を取り込んだ。
B4 の実行指示はまだない。⑤d の M15→G12 の範囲で続行する。

**一覧：済み 9／全体 42（うち追加 0）**。
M01〜M09 の厳密底上の主出力は検証済み。M19 は一般の芯のみで未完。
C01〜C03 に記載した既存構成の照合は法則の記録であり、一覧の全体には加算しない。
全族や相対テンソルの主型は、孤立した比較や条件付き Setup で置き換えない。

### 6.1 次の束の型（M10 の構成の分割）

まず同じ dg 加群・同じ準同型を持つ通常の相対圏の fiber と実 restriction を作る。
その恒等・合成の比較は、既存の加群制限の元の成分を保持する。
これは M10 の局所化前の材料であり、native CAlg 上の cocartesian fibration が
既に出来たとは数えない。高次の族と局所化・fiber 比較はこの後に接続する。
新しい ID は追加しない。

```lean
-- A : Type u; [CommRing A]; X Y Z : (operad A).Algebra
-- D_X := dgAlgebraCategory A ((assocForget A).obj X)
abbrev strictRawModuleCategory (X : (operad A).Algebra) := ModuleCategory A D_X

def strictRawModuleRelativeCategory (X : (operad A).Algebra) : RelativeCategory.{u+1}

def strictRawModuleRestrict (f : X ⟶ Y) :
  strictRawModuleCategory A Y ⥤ strictRawModuleCategory A X

def strictRawModuleRestrictRelative (f : X ⟶ Y) :
  strictRawModuleRelativeCategory A Y ⟶ strictRawModuleRelativeCategory A X

def strictRawModuleRestrict_idIso (X : (operad A).Algebra) :
  strictRawModuleRestrict (𝟙 X) ≅ 𝟭 (strictRawModuleCategory A X)

def strictRawModuleRestrict_compIso (f : X ⟶ Y) (g : Y ⟶ Z) :
  strictRawModuleRestrict g ⋙ strictRawModuleRestrict f ≅ strictRawModuleRestrict (f ≫ g)
```

単位・合成比較の成分の評価、自然性・結合・貼り合わせの法則は同じ束の法則として
型を追記する。200 行を超える証明があれば行数も記録する。

### 6.2 M10 の次の分割の型（着手前）

前節の同じ単位・合成比較の貼り合わせを使って、通常の相対族の全圏と射影を作る。
この型を含む擬関手の結合・左右単位の法則は、元の成分の評価によって照合する。

```lean
open scoped CategoryTheory.Bicategory
-- A : Type u; [CommRing A]
def strictRawModuleRestrictionPseudofunctor :
  LocallyDiscrete ((operad A).Algebraᵒᵖ) ⥤ᵖ Cat.{u, u+1}
abbrev strictRawModuleTotal :=
  Pseudofunctor.CoGrothendieck (strictRawModuleRestrictionPseudofunctor A)
def strictRawModuleProjection : strictRawModuleTotal A ⥤ (operad A).Algebra
```

この通常の Grothendieck 圏だけでは M10 の完成ではない。同じ相対圏の局所化と
元の dg nerve fiber の全比較、native CAlg 上の高次 transport は依然必要。
**一覧：済み 9／全体 42（うち追加 0）**。

### 6.3 同じ全圏の忘却・相対局所化の射影（着手前）

```lean
-- A : Type u; [CommRing A]
def strictRawModuleTotalForget : strictRawModuleTotal A ⥤ Complex A
-- 準同型は「底の BE 射が準同型、かつ同じ台の加群射が準同型」の同時条件。
def strictRawModuleTotalRelative : RelativeCategory.{u+1}
def strictRawModuleTotalProjectionRelative :
  strictRawModuleTotalRelative A ⟶ algebraRelativeCategory A
abbrev moduleTotalInfinity : SSet.{u+1}
def moduleTotalProjection : moduleTotalInfinity A ⟶ CAlg_R A
```

相対局所化の射影は元の全単体を持つ実写像として作り、頂点の写像だけでは済ませない。
ただし射影の cocartesian 性と fiber の同じ半自由 dg nerve との比較が残る限り、
この写像だけを `ModuleFamily` の完成として数えない。

### 6.4 実装の実測と追加法則の型

| 新設ファイル | 行 | 宣言 |
| --- | ---: | ---: |
| `StrictRawModules.lean` | 118 | 10 |
| `StrictRawCoherence.lean` | 125 | 6 |
| `StrictRawFamily.lean` | 102 | 3 |
| `TotalLocalization.lean` | 94 | 6 |

新設 4 本・439 行・25 宣言。累積 **21 本・1,988 行・108 宣言**
（private 3 を含む）。200 行を超える補題はない。型付き一覧に新しい ID を追加していない。

**一覧：済み 9／全体 42（うち追加 0）**。

準同型を保つ元の制限、単位・合成比較の恒等成分、その逆成分と左右単位・結合の
貼り合わせを検証した。この同じデータから擬関手と通常の全圏を構成した。
全圏の台は元の複体で、準同型条件は底と台の二つの準同型類の逆像の交わり。
局所化の射影の底は新しい代数模型ではなく、既存の cofibrant 置換を通した同じ CAlg_R。
新設 4 モジュールの対象ビルドは PASS。公開 25 宣言の小監査も PASS、
公理依存は全て `[propext, Classical.choice, Quot.sound]` のみ。
指定の `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` の内側で実行した。
最終対象ログは `/tmp/m15-total-localization3.log`（比較・全圏）と
`/tmp/m15-total-localization4.log`（射影）、監査は `/tmp/m15-audit6-verified.log`。
大きい監査・全体ビルドは行っていない。計算上限も引き上げていない。

M10 の未完の部分は、局所化の射影の cocartesian 性（必要なら同じ底上の
fibration 模型との比較も含む）、fiber の元の半自由 dg nerve との全比較、
その比較の厳密な単位・忘却・拡大との整合性。ここを仮定の欄に置かない。
M11〜M42 の残りと G12 はまだ完成していない。

以下は今回の構成と法則の実装の型。`strictRawModuleRelativeCategory` は対象を変えず
Hom だけを ULift し、元の準同型を down で引き戻す。

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawModules.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
variable (A : Type u) [CommRing A]

abbrev strictRawModuleCategory (X : (operad A).Algebra) :=
  ModuleCategory A (dgAlgebraCategory A ((assocForget A).obj X))

def strictRawModuleRelativeCategory (X : (operad A).Algebra) : RelativeCategory.{u+1}

variable {A}

def strictRawModuleRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleCategory A Y ⥤ strictRawModuleCategory A X

def strictRawModuleRestrictRelative {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRelativeCategory A Y ⟶ strictRawModuleRelativeCategory A X

def strictRawModuleRestrict_idIso (X : (operad A).Algebra) :
    strictRawModuleRestrict (𝟙 X) ≅ 𝟭 (strictRawModuleCategory A X)

def strictRawModuleRestrict_compIso {X Y Z : (operad A).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    strictRawModuleRestrict g ⋙ strictRawModuleRestrict f ≅ strictRawModuleRestrict (f ≫ g)

def strictRawModuleUnderlying (X : (operad A).Algebra) : strictRawModuleCategory A X ⥤ Complex A

lemma strictRawModuleHom_ext {X : (operad A).Algebra} {M T : strictRawModuleCategory A X}
    {f g : M ⟶ T} (h : (strictRawModuleUnderlying X).map f = (strictRawModuleUnderlying X).map g) :
    f = g

lemma strictRawModuleRestrict_idIso_eval (X : (operad A).Algebra) (M : strictRawModuleCategory A X) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).hom.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M)

lemma strictRawModuleRestrict_compIso_eval {X Y Z : (operad A).Algebra}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : strictRawModuleCategory A Z) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).hom.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawCoherence.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {A : Type u} [CommRing A]

lemma strictRawModuleRestrict_eval {X Y : (operad A).Algebra} (f : X ⟶ Y)
    {M T : strictRawModuleCategory A Y} (g : M ⟶ T) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict f).map g) =
      (strictRawModuleUnderlying Y).map g

lemma strictRawModuleRestrict_idIso_inv_eval (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).inv.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M)

lemma strictRawModuleRestrict_compIso_inv_eval {X Y Z : (operad A).Algebra}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : strictRawModuleCategory A Z) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).inv.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M)

lemma strictRawModuleRestrict_comp_assoc {W X Y Z : (operad A).Algebra}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerRight (strictRawModuleRestrict_compIso g h) (strictRawModuleRestrict f) ≪≫
        strictRawModuleRestrict_compIso f (g ≫ h) =
      Functor.associator (strictRawModuleRestrict h) (strictRawModuleRestrict g)
          (strictRawModuleRestrict f) ≪≫
        isoWhiskerLeft (strictRawModuleRestrict h) (strictRawModuleRestrict_compIso f g) ≪≫
        strictRawModuleRestrict_compIso (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.assoc f g h))

lemma strictRawModuleRestrict_comp_id {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRestrict_compIso f (𝟙 Y) ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.comp_id f)) =
      isoWhiskerRight (strictRawModuleRestrict_idIso Y) (strictRawModuleRestrict f) ≪≫
        Functor.leftUnitor (strictRawModuleRestrict f)

lemma strictRawModuleRestrict_id_comp {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRestrict_compIso (𝟙 X) f ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.id_comp f)) =
      isoWhiskerLeft (strictRawModuleRestrict f) (strictRawModuleRestrict_idIso X) ≪≫
        Functor.rightUnitor (strictRawModuleRestrict f)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawFamily.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
variable (A : Type u) [CommRing A]

def strictRawModuleRestrictionPseudofunctor :
    LocallyDiscrete ((operad A).Algebraᵒᵖ) ⥤ᵖ Cat.{u, u+1}

abbrev strictRawModuleTotal := Pseudofunctor.CoGrothendieck
  (strictRawModuleRestrictionPseudofunctor A)

def strictRawModuleProjection : strictRawModuleTotal A ⥤ (operad A).Algebra
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/TotalLocalization.lean`：

```lean
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.SimplicialLocalization
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
attribute [local implicit_reducible] strictRawModuleRestrictionPseudofunctor
variable (A : Type u) [CommRing A]

def strictRawModuleTotalForget : strictRawModuleTotal A ⥤ Complex A

def strictRawModuleTotalRelative : RelativeCategory.{u+1}

def strictRawModuleTotalProjectionRelative :
    strictRawModuleTotalRelative A ⟶ algebraRelativeCategory A

abbrev moduleTotalInfinity : SSet.{u+1}

instance moduleTotalInfinity_quasicategory : Quasicategory (moduleTotalInfinity A)

def moduleTotalProjection : moduleTotalInfinity A ⟶ CAlg_R A
```

## 7. M10 の固定底の fiber と全圏への包含（11-14、着手前）

main の `b2d198488` までの文書を取り込んだ。B4 の実行指示はまだない。
M10 の既存構成の分割として、同じ固定底の加群圏の包含と、通常の fiber の比較を作る。
Mathlib の同じ擬関手の Grothendieck 構成が持つ包含・Cartesian lift・fiber 同値を再利用する。
native な局所化後の fiber 同値や cocartesian 性を、この通常圏の結果で代用しない。

**一覧：済み 9／全体 42（うち追加 0）**。

```lean
-- A : Type u; [CommRing A]; X Y : (operad A).Algebra; f : X ⟶ Y
def strictRawModuleFiberInclusion (X : (operad A).Algebra) :
  strictRawModuleCategory A X ⥤ strictRawModuleTotal A

lemma strictRawModuleFiberInclusion_projection (X : (operad A).Algebra) :
  strictRawModuleFiberInclusion A X ⋙ strictRawModuleProjection A =
    (Functor.const (strictRawModuleCategory A X)).obj X

lemma strictRawModuleFiberInclusion_forget (X : (operad A).Algebra) :
  strictRawModuleFiberInclusion A X ⋙ strictRawModuleTotalForget A = strictRawModuleUnderlying X

def strictRawModuleFiberEquivalence (X : (operad A).Algebra) :
  strictRawModuleCategory A X ≌ Functor.Fiber (strictRawModuleProjection A) X

def strictRawModuleFiberInclusionRelative (X : (operad A).Algebra) :
  strictRawModuleRelativeCategory A X ⟶ strictRawModuleTotalRelative A

def strictRawModuleFiberBaseRelative (X : (operad A).Algebra) :
  strictRawModuleRelativeCategory A X ⟶ algebraRelativeCategory A

lemma strictRawModuleFiberInclusionRelative_projection (X : (operad A).Algebra) :
  strictRawModuleFiberInclusionRelative A X ≫ strictRawModuleTotalProjectionRelative A =
    strictRawModuleFiberBaseRelative A X

def moduleRawFiberInclusion (X : (operad A).Algebra) :
  localizationNerve (strictRawModuleRelativeCategory A X) ⟶ moduleTotalInfinity A
-- 同じ相対関手の全単体での射影可換式も構成する。
```

単位比較の逆成分が同じ台で恒等になる §6 の法則を使い、包含と台の忘却を
厳密な関手等式で接続する。相対包含の準同型保存はこの等式から供給する。

### 7.1 同じ通常の Cartesian lift の相対性（着手前）

続いて M10 の既存の Grothendieck 構成の Cartesian lift の法則を使う。
元の制限が同じ台を保つため、その標準 lift の台は恒等射であり、底の射が弱同値なら
標準 lift は全圏の指定準同型となる。これは局所化後の底の弱同値の反転に使う法則。

```lean
instance strictRawModuleProjection_isFibered : IsFibered (strictRawModuleProjection A)

def strictRawModuleCartesianLift (f : X ⟶ Y) (M : strictRawModuleCategory A Y) :
  (strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M) ⟶
    (strictRawModuleFiberInclusion A Y).obj M

lemma strictRawModuleCartesianLift_isStronglyCartesian (f : X ⟶ Y)
  (M : strictRawModuleCategory A Y) :
  IsStronglyCartesian (strictRawModuleProjection A) f (strictRawModuleCartesianLift A f M)

lemma strictRawModuleCartesianLift_underlying (f : X ⟶ Y)
  (M : strictRawModuleCategory A Y) :
  (strictRawModuleTotalForget A).map (strictRawModuleCartesianLift A f M) =
    𝟙 ((strictRawModuleUnderlying Y).obj M)

lemma strictRawModuleCartesianLift_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalRelative A).weakEquivalences
      ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
        (strictRawModuleCartesianLift A f M))
```

これは通常の Cartesian 性の法則で、native な cocartesian 性は依然別に証明する。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.2 同じ正則加群の section（着手前）

M05・M10 の同じ正則加群を全圏へ載せる分割として、既存の
`representableRestrictionMap` により通常の section を構成する。
この射の同じ台は元の BE 代数射そのものなので、section は準同型を保つ。

```lean
-- A : Type u; [CommRing A]
def strictRawRegularObject (X : (operad A).Algebra) : strictRawModuleTotal A

def strictRawRegularMap (f : X ⟶ Y) : strictRawRegularObject A X ⟶ strictRawRegularObject A Y

lemma strictRawRegularMap_underlying (f : X ⟶ Y) :
  (strictRawModuleTotalForget A).map (strictRawRegularMap A f) = f.hom

def strictRawModuleUnitSection : (operad A).Algebra ⥤ strictRawModuleTotal A

lemma strictRawModuleUnitSection_projection :
  strictRawModuleUnitSection A ⋙ strictRawModuleProjection A = 𝟭 (operad A).Algebra

def strictRawModuleUnitSectionRelative : algebraRelativeCategory A ⟶ strictRawModuleTotalRelative A

lemma strictRawModuleUnitSectionRelative_projection :
  strictRawModuleUnitSectionRelative A ≫ strictRawModuleTotalProjectionRelative A = 𝟙 (algebraRelativeCategory A)

def moduleUnitSection : CAlg_R A ⟶ moduleTotalInfinity A
-- 同じ section の局所化射影との全単体での合成式も検証する。
```

正則加群の台・恒等・合成の法則と全圏の射の外延性を、この同じ構成の法則として
記録する。局所化後の fiber 同値が完成するまで、既存の半自由模型の単位との
全比較が終わったとは数えない。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.3 同じ相対局所化の係数移送の法則（着手前）

M10 で同じ全代数模型と cofibrant 模型を移すため、既存の自由 hammock の
augmentation・比較の係数自然性から、同じ局所化 Hom 射の弱同値性へ移す法則を使う。
これは既存の相対局所化関手の係数移送であり、新しいモデル構造は構成しない。

```lean
-- C D : RelativeCategory.{u}; F : C ⟶ D
lemma localizationHomMap_weak_of_hammock (X Y : C.category)
  (h : IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
  IsWeakHomotopyEquivalence (localizationHomMap F X Y)

lemma localizationNerveMap_fullyFaithful_of_hammock
  (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
  IsFullyFaithful (localizationNerveMap F)

-- G : D ⟶ C; ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category
lemma localizationNerveMap_essentiallySurjective_of_counit
  (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
  IsEssentiallySurjective (localizationNerveMap F)

lemma localizationNerveMap_isQCatEquivalence_of_hammock_counit
  (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y))
  (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
  IsQCatEquivalence (localizationNerveMap F)
```

両合成から恒等への元の弱自然変換がある場合の既存の hammock 判定を、この同じ
全 nerve へ移す系も記録する。元の全関手・Hom 射を保持する係数移送であり、
対象ごとの比較や h 上の同値には弱めない。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.4 同じ BE 底の模型の係数移送への適用（着手前）

前節の既存局所化の法則を、⑤a の元の二つの相対関手と指定弱比較に適用する。
⑤a のソースは変更しない。

```lean
lemma cAlgToAlgebraLocalization_isQCatEquivalence :
  IsQCatEquivalence (localizationNerveMap (cofibrantToAlgebraDKRelative A))
lemma algebraLocalizationToCAlg_isQCatEquivalence :
  IsQCatEquivalence (localizationNerveMap (algebraToCofibrantDKRelative A))
lemma moduleUnitSection_projection_isQCatEquivalence :
  IsQCatEquivalence (moduleUnitSection A ≫ moduleTotalProjection A)
```

二つの関手が同値であることだけでは、指定弱自然変換の全関手圏での回収や、
正則加群の実関手が指定された恒等底上の section となる全比較は完成しない。
その比較と native fiber・cocartesian 性は引き続き必要。
**一覧：済み 9／全体 42（うち追加 0）**。

### 7.5 検証済みの結果と実際の型（2026-11-14）

§7〜§7.4 の五ファイルを対象ビルドで検証した。今回追加は 491 行・33 宣言、
累計は新規 Lean 26 ファイル・2,479 行・141 宣言（private 3 を含む）。
IS-W2 §14 と同じソース全行で数え、200 行を超える補題はない。
外枠 17,000 行、約 8,500 行での途中報告の規約を維持する。

全て `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` の下で実行し、
五ファイルの対象ビルドと今回の公開 33 宣言の小さい公理監査が通過した。
監査の実出力は 33 件あり、依存公理は `propext`・`Classical.choice`・`Quot.sound`
のみ。`sorryAx`・追加公理はない。大きい監査は実施していない。
通常の fiber 同値と Cartesian lift、正則加群の実関手、
同じ二つの BE 底の局所化関手自身の準圏同値性までを得た。
指定弱自然変換の全関手圏での回収、半自由の native fiber との比較と
native cocartesian 性は依然未完了なので、M10 は完了に数えない。

既存の構成の係数移送・射影・自然性・合成則の分割として、今回の実際の宣言の型を
以下に記録する。共通文脈は各ソースの `universe u`、`A : Type u`、`[CommRing A]`、
および明記した名前空間・変数である。新しい一次 ID は追加しない。

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawFiber.lean`（121 行・9 宣言）：

```lean
def strictRawModuleFiberInclusion (X : (operad A).Algebra) :
    strictRawModuleCategory A X ⥤ strictRawModuleTotal A

lemma strictRawModuleFiberInclusion_projection (X : (operad A).Algebra) :
    strictRawModuleFiberInclusion A X ⋙ strictRawModuleProjection A =
      (Functor.const (strictRawModuleCategory A X)).obj X

lemma strictRawModuleFiberInclusion_forget (X : (operad A).Algebra) :
    strictRawModuleFiberInclusion A X ⋙ strictRawModuleTotalForget A = strictRawModuleUnderlying X

def strictRawModuleFiberEquivalence (X : (operad A).Algebra) :
    strictRawModuleCategory A X ≌ Functor.Fiber (strictRawModuleProjection A) X

def strictRawModuleFiberInclusionRelative (X : (operad A).Algebra) :
    strictRawModuleRelativeCategory A X ⟶ strictRawModuleTotalRelative A

def strictRawModuleFiberBaseRelative (X : (operad A).Algebra) :
    strictRawModuleRelativeCategory A X ⟶ algebraRelativeCategory A

lemma strictRawModuleFiberInclusionRelative_projection (X : (operad A).Algebra) :
    strictRawModuleFiberInclusionRelative A X ≫ strictRawModuleTotalProjectionRelative A =
      strictRawModuleFiberBaseRelative A X

def moduleRawFiberInclusion (X : (operad A).Algebra) :
    localizationNerve (strictRawModuleRelativeCategory A X) ⟶ moduleTotalInfinity A

lemma moduleRawFiberInclusion_projection (X : (operad A).Algebra) :
    moduleRawFiberInclusion A X ≫ moduleTotalProjection A =
      localizationNerveMap (strictRawModuleFiberBaseRelative A X ≫ algebraToCofibrantDKRelative A)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRawCartesian.lean`（78 行・5 宣言）：

```lean
instance strictRawModuleProjection_isFibered : IsFibered (strictRawModuleProjection A)

def strictRawModuleCartesianLift {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    (strictRawModuleFiberInclusion A X).obj ((strictRawModuleRestrict f).obj M) ⟶
      (strictRawModuleFiberInclusion A Y).obj M

lemma strictRawModuleCartesianLift_isStronglyCartesian {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    IsStronglyCartesian (strictRawModuleProjection A) f (strictRawModuleCartesianLift A f M)

lemma strictRawModuleCartesianLift_underlying {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalForget A).map (strictRawModuleCartesianLift A f M) =
      𝟙 ((strictRawModuleUnderlying Y).obj M)

lemma strictRawModuleCartesianLift_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) (M : strictRawModuleCategory A Y) :
    (strictRawModuleTotalRelative A).weakEquivalences
      ((ULiftHom.up.{u,u+1,u+1} (C := strictRawModuleTotal A)).map
        (strictRawModuleCartesianLift A f M))
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/StrictRegularSection.lean`（137 行・11 宣言）：

```lean
-- M T : strictRawModuleTotal A; f g : M ⟶ T（hom_ext の暗黙引数）
lemma strictRawModuleTotal_hom_ext {M T : strictRawModuleTotal A} {f g : M ⟶ T}
    (hb : (strictRawModuleProjection A).map f = (strictRawModuleProjection A).map g)
    (hv : (strictRawModuleTotalForget A).map f = (strictRawModuleTotalForget A).map g) : f = g

def strictRawRegularObject (X : (operad A).Algebra) : strictRawModuleTotal A

lemma strictRawRegularObject_underlying (X : (operad A).Algebra) :
    (strictRawModuleTotalForget A).obj (strictRawRegularObject A X) = X.carrier

def strictRawRegularMap {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawRegularObject A X ⟶ strictRawRegularObject A Y

lemma strictRawRegularMap_underlying {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    (strictRawModuleTotalForget A).map (strictRawRegularMap A f) = f.hom

def strictRawModuleUnitSection : (operad A).Algebra ⥤ strictRawModuleTotal A

lemma strictRawModuleUnitSection_projection :
    strictRawModuleUnitSection A ⋙ strictRawModuleProjection A = 𝟭 (operad A).Algebra

def strictRawModuleUnitSectionRelative : algebraRelativeCategory A ⟶ strictRawModuleTotalRelative A

lemma strictRawModuleUnitSectionRelative_projection :
    strictRawModuleUnitSectionRelative A ≫ strictRawModuleTotalProjectionRelative A =
      𝟙 (algebraRelativeCategory A)

def moduleUnitSection : CAlg_R A ⟶ moduleTotalInfinity A

lemma moduleUnitSection_projection :
    moduleUnitSection A ≫ moduleTotalProjection A =
      localizationNerveMap (cofibrantToAlgebraDKRelative A ≫ algebraToCofibrantDKRelative A)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/AlgebraModelComparison.lean`（53 行・3 宣言）：

```lean
lemma cAlgToAlgebraLocalization_isQCatEquivalence :
    IsQCatEquivalence (localizationNerveMap (cofibrantToAlgebraDKRelative A))

lemma algebraLocalizationToCAlg_isQCatEquivalence :
    IsQCatEquivalence (localizationNerveMap (algebraToCofibrantDKRelative A))

lemma moduleUnitSection_projection_isQCatEquivalence :
    IsQCatEquivalence (moduleUnitSection A ≫ moduleTotalProjection A)
```

`SerrePositivity/EInfinity/Modules/RelativeLocalizationEquivalence.lean`（102 行・5 宣言）：

```lean
variable {C D : RelativeCategory.{u}} (F : C ⟶ D) (G : D ⟶ C)
lemma localizationHomMap_weak_of_hammock (X Y : C.category)
    (h : IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
    IsWeakHomotopyEquivalence (localizationHomMap F X Y)

lemma localizationNerveMap_fullyFaithful_of_hammock
    (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y)) :
    IsFullyFaithful (localizationNerveMap F)

lemma localizationNerveMap_essentiallySurjective_of_counit
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsEssentiallySurjective (localizationNerveMap F)

lemma localizationNerveMap_isQCatEquivalence_of_hammock_counit
    (h : ∀ X Y, IsWeakHomotopyEquivalence (Hammock.Relative.colimitMap F X Y))
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category)
    (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsQCatEquivalence (localizationNerveMap F)

lemma localizationNerveMap_isQCatEquivalence_of_weak_comparisons
    (η : F.functor ⋙ G.functor ⟶ 𝟭 C.category) (hη : ∀ X, C.weakEquivalences (η.app X))
    (ε : G.functor ⋙ F.functor ⟶ 𝟭 D.category) (hε : ∀ Y, D.weakEquivalences (ε.app Y)) :
    IsQCatEquivalence (localizationNerveMap F)
```

**一覧：済み 9／全体 42（うち追加 0）**。

## 8. M10 の同じ底の弱比較を全関手間へ移す分割（11-14）

§7 の二つの係数関手について、同じ弱自然変換の通常の円筒を局所化する。
円筒の指定弱射は元の圏への射影の逆像であり、射影の逆候補には零端点を使う。
元の弱縮約と厳密な端点・射影の合成則から、同じ射影の局所化が同値になる。
その全関手単体集合の同型を同じ円筒関手で後合成して、
元の二つの局所化関手間の `FunctorIso` を得る。
これは既存の相対局所化の自然性・係数移送・単位・余単位の法則の証明の分割。
新しい一次 ID は追加しない。

元の `cofibrantDKComparison` と `algebraDKComparison` に適用して、
順方向・逆方向とも元の相対関手のままの `QCatEquivalence` を組み立てる。
同じ正則加群の実関手と射影の合成から恒等への全関手間の可逆比較も得る。
各頂点でのこの比較と元の指定弱辺の比較は引き続き照合し、
半自由 native fiber との比較・native cocartesian 性も残す。
したがって M10 は未完了である。

以下に追加する法則の実際の型を記録する。`C D : RelativeCategory.{u}`、
`F G : C ⟶ D`、BE 適用では `A : Type u` と `[CommRing A]` を共通文脈とする。

`SerrePositivity/EInfinity/Modules/RelativeCylinderLaws.lean`（89 行・7 宣言）：

```lean
def relativeCylinder : RelativeCategory.{u}

def relativeCylinderProjection : relativeCylinder C ⟶ C

def relativeCylinderEndpoint (i : Fin 2) : C ⟶ relativeCylinder C

lemma relativeCylinderEndpoint_projection (i : Fin 2) :
    relativeCylinderEndpoint C i ≫ relativeCylinderProjection C = 𝟙 C

def relativeCylinderContraction :
    (relativeCylinderProjection C).functor ⋙ (relativeCylinderEndpoint C 0).functor ⟶
      𝟭 (relativeCylinder C).category

lemma relativeCylinderContraction_weak (X : (relativeCylinder C).category) :
    (relativeCylinder C).weakEquivalences ((relativeCylinderContraction C).app X)

lemma relativeCylinderProjection_isQCatEquivalence :
    IsQCatEquivalence (localizationNerveMap (relativeCylinderProjection C))
```

`SerrePositivity/EInfinity/Modules/RelativeNaturalComparison.lean`（103 行・5 宣言）：

```lean
def relativeCylinderEndpointIso :
    FunctorIso (localizationNerveMap (relativeCylinderEndpoint C 0))
      (localizationNerveMap (relativeCylinderEndpoint C 1))

def relativeNaturalCylinder (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) : relativeCylinder C ⟶ D

lemma relativeNaturalCylinder_zero (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    relativeCylinderEndpoint C 0 ≫ relativeNaturalCylinder η hη = F

lemma relativeNaturalCylinder_one (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    relativeCylinderEndpoint C 1 ≫ relativeNaturalCylinder η hη = G

def localizationNerveMapIsoOfWeakNatTrans (η : F.functor ⟶ G.functor)
    (hη : ∀ X, D.weakEquivalences (η.app X)) :
    FunctorIso (localizationNerveMap F) (localizationNerveMap G)
```

`SerrePositivity/EInfinity/BarrattEccles/Modules/AlgebraRoundTripComparison.lean`（70 行・4 宣言）：

```lean
def cAlgModelRoundTripIso :
    FunctorIso (localizationNerveMap (cofibrantToAlgebraDKRelative A) ≫
      localizationNerveMap (algebraToCofibrantDKRelative A)) (𝟙 (CAlg_R A))

def algebraModelRoundTripIso :
    FunctorIso (localizationNerveMap (algebraToCofibrantDKRelative A) ≫
      localizationNerveMap (cofibrantToAlgebraDKRelative A))
      (𝟙 (localizationNerve (algebraRelativeCategory A)))

def cAlgAlgebraModelEquivalence :
    QCatEquivalence (CAlg_R A) (localizationNerve (algebraRelativeCategory A))

def moduleUnitSection_projectionIso :
    FunctorIso (moduleUnitSection A ≫ moduleTotalProjection A) (𝟙 (CAlg_R A))
```

### 8.1 実測と対象ビルド

§8 の追加は新規 Lean 3 ファイル・262 行・16 宣言。
累計は新規 Lean 29 ファイル・2,741 行・157 宣言（private 3 を含む）。
200 行を超える補題はない。一次 ID の追加はなく、M10 の同じ構成の法則の分割として扱う。
円筒の法則、同じ弱自然変換の局所化比較、BE 底の往復比較の三ファイルを
指定された共有鍵の下で対象ビルドし、全て通過した。

残る境界は、得た全関手比較の指定頂点での辺との照合、
同じ台・単位・随伴を保持した半自由 native fiber の比較と全族の native cocartesian 性。
M11 以降、RHom・完備反射・完備テンソルも引き続き未完。

**一覧：済み 9／全体 42（うち追加 0）**。

今回の公開 16 宣言の小さい公理監査も、指定の共有鍵の下で通過した。
`#print axioms` の実出力は 16 件で、依存公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。`sorryAx`・追加公理はない。
大きい監査や全体ビルドは実施していない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 9. 同じ自由局所化の係数移送の単位・合成則と B4（11-14）

M10 の指定局所化辺との照合に向け、既存の自由 hammock の係数写像について、
各自由次数の固定端点の写像との一致・空語の単位・全連結合成の保存を証明した。
対象ビルドは指定共有鍵の下で通過。新規 Lean 1 ファイル・78 行・3 宣言、
累計は 30 ファイル・2,819 行・160 宣言（private 3 を含む）。
一次 ID は増やさず、既存の係数移送の法則として扱う。
全 nerve の係数作用と源の自然性の二ファイルは未検証の下書きで、まだ実測に含めない。

着手中、main の `citation-attributes.md` §14（ab311d2d1）で B4 の手順が公開された。
⑤d も同じ手順の対象と明記されているため、M10 の Lean を区切って B4 を優先する。
取り込み前のソースと参照の採取・保留 0 のプレビューを先に行い、main の取り込み後に
対象ビルドと小さい監査を行う。未検証の下書きは保持する。

```lean
lemma freeHammockCoefficient_fixedColimitMap (X Y : C.category) (n : SimplexCategoryᵒᵖ) :
    (freeHammockMap F X Y).app n =
      Hammock.Relative.fixedColimitMap ((freeResolutionMap F).app n)
        (freeResolutionMap_object F n X) (freeResolutionMap_object F n Y)

lemma freeHammockCoefficient_unit (X : C.category) :
    freeHammockDiagonalUnit C X ≫ freeHammockDiagonalMap F X X =
      freeHammockDiagonalUnit D (F.functor.obj X)

lemma freeHammockCoefficient_comp (X Y Z : C.category) :
    freeHammockDiagonalComposition C X Y Z ≫ freeHammockDiagonalMap F X Z =
      (freeHammockDiagonalMap F X Y ⊗ₘ freeHammockDiagonalMap F Y Z) ≫
        freeHammockDiagonalComposition D (F.functor.obj X) (F.functor.obj Y) (F.functor.obj Z)
```

**一覧：済み 9／全体 42（うち追加 0）**。

## 10. B4：保留 2 件で停止（2026-11-14 昼）

`citation-attributes.md` §14・`bulk-w1-b3/B4-README.md` と調整役の指示に従い、
M15 の作業を区切って B4 を優先した。検証済みは `8593cc4b9` までコミット済み。
基準 `c5c4436c0` からこの枝で追加・変更したコミット済み Lean の Git 差分は
**30 ファイル**。未追跡の未検証下書き二つ（`FreeHammockCoefficientNerve.lean`、
`LocalizationSourceNaturality.lean`）は原文を別保存して作業木に保持した。

最初の採取は、Lake の依存の再ビルド要求で終了した。採取条件は外さず、
要求された五つと、その上の枝固有モジュールの正規 Lake 成果物を整え、
検証済み 30 モジュールの対象ビルドを通した。main の作業木には書き込んでいない。
その後 `bulk_namespace.py collect` を `--class impl --wait 3600`、
各組 `gtimeout --kill-after=3s 280` の下で 4 本・8 本・8 本に分けて実行し、
**20 ファイルの採取が成功**した。各索引内の原文・保存した原文・作業木のソースの
全バイト一致を再確認した。採取時の Lake options と脚本のハッシュも索引に残した。

`bulk_namespace.py rewrite` の最初の 4 本・次の 8 本は保留 0。
続く 8 本のプレビューでは、次の二つが保留になったため、**ここで B4 を止めた**。

| ファイル | 行 | 保留になった open |
| --- | --- | --- |
| `EInfinity/BarrattEccles/Modules/StrictUnderlyingComparison.lean` | 27 | `SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison` |
| `EInfinity/BarrattEccles/Modules/StrictUnderlyingRestriction.lean` | 23 | 同じ名前空間 |

両方の理由は `explicit opens policy needed for a renamed namespace`。
前者で採取された同名前空間の使用宣言は `complexClosedPresentation`、
`complexClosedPresentation_ring_evaluation`、`complexDerivedEvaluation`、
`semifreePointEquivalence`。後者は `semifreePointEquivalence`。
この open の方針を調整役が確認する必要がある。こちらで保留を消す置換はしていない。

main は **未取り込み**、プレビューのソースへの反映も **未実施**。
残り 10 ファイルの採取と、取り込み後の対象ビルド・小さい監査は未実施で、
B4 は完了していない。保存資料は
[`b4-m15-2026-11-14/summary.json`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/summary.json)、
[`review.json`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/review.json)、
[`before-index.json.gz`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/before-index.json.gz)、
[`checked-preview.diff.gz`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/checked-preview.diff.gz)。
索引は取り込み前の原文に限って有効であり、取り込み後のソースには流用しない。

M15 の一覧・型・ソースには B4 の変更をまだ加えていない。
累計は検証済み新規 Lean 30 ファイル・2,819 行・160 宣言（private 3 を含む）。

**一覧：済み 9／全体 42（うち追加 0）**。

## 11. B4 停止中の代替作業：A5 と M15 の実際の型の受け渡し（11-14、紙）

main `efa846fe8` の改名表の SHA は §10 のものと同じで、
`DiagramComparison` の明示的な open 方針はまだない。保留 2 件を維持し、
main の取り込み・プレビュー反映・M15 の Lean は再開していない。
`lane-goals-2026-11-14.md` の⑤dの代替作業に従って、A5 を読み取りだけで照合した。
ここでいう drafts は全て `formalization-plans/bhatt-scholze/drafts/` 以下。
読み取った次の七ファイルは、自分の枝と main の間で差分がないことも確認した。

- `Shared/Descendable.lean`
- `A5/StrongDescent.lean`、`A5/WeaklyInitialAndDescent.lean`
- `A4/Perfectoidization.lean`、`A2/DerivedPrismaticCohomology.lean`
- `DerivedGeneral/CompletionFunctor.lean`、`DerivedGeneral/Truncation.lean`

以下は §1 の既存出力の接続条件と利用側の差の記録であり、
新しい一次 ID・Lean 宣言・追加の仮定を導入したものではない。

### 11.1 BE 中核で進める範囲と、現在の実装の境界

本体の `BarrattEccles/Theory.lean:35` の `barrattEcclesCore.CAlg A` は
実際の `CAlg_R A`、その忘却は `cAlgForgetDerived A` に固定されている。
一方、`drafts/Shared/BarrattEcclesTheory.lean:28` の `barrattEcclesTheory` は
作業用の `sorry` を含み、本体の `barrattEcclesTheoryOfRemaining` は G12 などの
未供給欄を引数に取る。これを M15 の実装入力にすると、M15 の後に行う G12 を
先に要求する依存になる。D80 の指定どおり M15 の本体は実 `CAlg_R A` と中核で作り、
A5 の `E := barrattEcclesTheory` 特殊化は全界面の組み立て後の利用側の接続とする。
任意 E への輸送を作る理由にはしない。

現在の実出力の型は、厳密な BE 代数 `X Y : (operad A).Algebra` に対する
`strictModuleInfinity A X`、`strictModuleUnderlying A X`、`strictModuleUnit A X`、
`strictModuleExtend f`・`strictModuleRestrict f` とその随伴・同じ台の比較である。
M10 の実射影には

```lean
moduleUnitSection_projectionIso A :
  FunctorIso (moduleUnitSection A ≫ moduleTotalProjection A) (𝟙 (CAlg_R A))
```

を構成済み。しかしこの型は、任意の native な底 `R : (CAlg_R A) _⦋0⦌` の
指定 fiber の相対テンソル・内部 Hom や、その fiber の単位を供給する型ではない。
A5 の `deltaRootEdge` を厳密な一つの代数射の代表に取り替えて使う接続もまだない。
M10・C02 が指定した同じ U・単位・随伴と高次単体を保持する全族を作る必要が残る。

### 11.2 共通の厚さと Shared の厚さは定義上の等式ではない

本体の `InfinityCategories/HA/StableInfinityCategories/Thick.lean:27` は
零・同型・実 cofiber/fiber・ホモトピー圏の retract で閉じる `IsThick`。
`EInfinity/Modules/ThickTensorIdeal.lean:25` はこれを拡張し、
右からの `tensorWith M` の閉性を加える。
Shared の同名構造（`Shared/Descendable.lean:59`）は、全ての有限単体集合 K の
`JoinCocone` に対する有限余極限閉性、辺で表示した retract、shift、tensor を持つ。

M19 の接続では、有限余極限閉性と cofiber/fiber 閉性の相互変換、
`Nonempty (Retract (ho.mk x) (ho.mk y))` と二つの実辺・合成式の変換、
同型で移した頂点の所属を保持する法則が必要。
同じ名前であることや、生成閉包が双方とも述語の交わりであることだけでは、
M22 の単位底特殊化の述語の一致にはならない。この互換の証明は未実装である。

### 11.3 完備圏の単位：A 自身が完備でない離散底も残す

`Shared/Descendable.lean:302` の `isDescendable_complete` は、s と B を受け、
B の台の s 完備性だけを仮定する。底の環 A 自身の s 完備性は引数にない。
その結論の `IsDescendableComplete` は、完備テンソルイデアルが
**単位 A の完備化**を含むという定義（同ファイル:297）である。

これに対し §1.5 の M39 は一般の底 R・終域 B の台の完備性を仮定する。
従って R を離散底の単位 A に特殊化して M39 だけを当てる経路には、
利用側にない A の完備性が余分に必要になる。
§1.5 で約束した離散版全型の互換出力を保つには、M36・M37 の反射・テンソルの
法則から「生成元と単位を反射した thick イデアル」へ移す接続も必要。
Shared に A の完備性を追加して穴を埋めない。

接続条件の模式的な型を §1.5 の記法で固定する（下の名前はまだ Lean 宣言ではない）：

```lean
-- C_R, one_R, U_R, moduleCompletion, inclusion は M10・M36 の出力。
completeUnit R s : (completeModules R s) _⦋0⦌ :=
  (moduleCompletion R s).app (Opposite.op ⦋0⦌) one_R

FunctorIso
  (moduleCompletion R s ≫ completeModulesInclusion R s ≫ U_R)
  (U_R ≫ Derived.completion A s)

FunctorIso (completeTensorWith R s (completeUnit R s))
  (𝟙 (completeModules R s))
```

R の台が完備な場合に `completeUnit` の忘却と `one_R` を比較する。
その仮定がない場合の単位は反射した単位として保持する。
これは M36・M37 の同じ構成の単位・係数移送の法則であり、
通常版と完備版の descendability の同値を定義にする変更ではない。

### 11.4 A5 の Amitsur データは完備圏で組み立てる必要がある

`A4/Perfectoidization.lean:344–349` の `directPerfectionFunctor` は
`completePerfectionFunctor ≫ completeCAlgInclusion`。
`A2/DerivedPrismaticCohomology.lean:66–70` の完備 CAlg は、
忘却した台が p と prism の generator で完備である充満部分準圏。
`A5/WeaklyInitialAndDescent.lean:302–307` の結論は、この包含後の同じ
根被覆増大錐 c の `IsLimitCone c` を要求している。

一方 `Shared/Descendable.lean:179–189` の `AmitsurData.term n` は、
**通常の CAlg** における各段の `IsColimitCone` を要求する。
完備テンソルで作った各段を包含で通常の CAlg に送っただけでは、この引数を得ない。
包含の極限保存と余極限保存を混同しない。

接続経路は M42 の `CompleteAmitsurData` を完備圏で構成し、
その同じ増大・base・zero・leg・全 term を使って完備圏での極限性を得た後、
包含の極限保存で A5 が表示する c の極限性へ送るものとして記録する。
指定された root-cover の脚を別の Amitsur 図式に置き換えない。
この経路のために A5 の降下述語を完備版へ接続する判断は利用側に残り、
完備版の降下を通常版の `IsDescendableOver` の証明済み結果とは数えない。
M41 も同様に、完備な射の圏で与えられた余錐の `IsColimitCone` をその圏で使う。
通常の射の圏との比較は別途供給する。

### 11.5 RHom の係数と零次評価の接続

`A5/StrongDescent.lean:97` の `fiberSquareRHom f L` は
`U_R RHom_R(F ⊗_R F, moduleFromBase R L)` の型を要求する。
同ファイル:101 の `rootDual` の L は `moduleHeartVertex A (ModuleCat.of A A)`。
これを `U_R RHom_R(F ⊗_R F, one_R)` と比較するためには、M34 の係数作用の単位則

```lean
-- §1.5 の記法。M34 の同じ係数作用の未実装の単位法則。
VertexIso
  ((moduleFromBase R).app (Opposite.op ⦋0⦌) (unitComplex A))
  one_R
```

が要る。構成済みの `strictModuleUnitUnderlyingIso` は厳密底 X 上の
正則加群の**台**を `complexDerivedEvaluation A X.carrier` と比較する型であり、
この一般 R 加群の係数作用の単位則の代わりにはならない。

`DerivedGeneral/Truncation.lean:53` の `IsConnectiveAt A (-1) x` は
`∀ i, -1 < i → Subsingleton (derivedInfinityHomology A i x)`。
M33 の加法的な零次 Hom 比較で i=0 の零性へ移し、
M35 は指定された `fiberPowerMap f 2` の零性と接続する。
Shared の `hasDescentIndexLEOver_two_of_rhom : True`（同ファイル:202）は
この入力・出力を全く持たないため、呼び出し名があるだけでは API ではない。

任意の離散 L を使う `squareZero_rhom_coconnective` と
`rhom_baseChange_koszul_connection` の係数はそのまま保持する。
双対可能な Koszul K での Hom–tensor 比較と、任意 L に対する比較を分ける。
Koszul の計算、最高次の全射、Nakayama、(p,d) と
(p,φ⁻¹(d)) の完備性を結ぶ A5 の個々の証明は A5 に残す。

### 11.6 変更・検証の範囲

今回変更したのはこの紙の報告だけ。drafts・Lean ソース・B4 の保存索引は変更していない。
Lean の新しい対象ビルド・監査は実施していない。B4 の保留は引き続き 2 件。
新規 Lean の実測は 30 ファイル・2,819 行・160 宣言のまま。
M10 以降と RHom・完備反射・完備テンソルを完了に数えていない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 12. B4 の同一保留の第3回確認とゴールの blocked 判定（11-14）

§10 の初回停止、§11 の代替作業時の再確認に続いて、
main `efa846fe8` と現在の改名表を再確認した。
`namespace-rewrite-map.json` の SHA は引き続き
`67ba053988c420d4a43dc026da90b93dca531e393c94bcfce7ca420673bd9d87`。
`DiagramComparison` の明示的な `opens` 方針も、保留となった二モジュールの
`module_opens` 方針も追加されていない。

取り込み前の原文が保存索引と一致することを確認し、同じ八ファイルの manifest と
同じ採取範囲の索引を使って、現行の `bulk_namespace.py rewrite` を再実行した。
終了コード 1 と `review.json` に、§10 と同じ二か所・同じ理由の保留を再現した。
これは生存中のジョブの待機ではなく、未解決の open 方針による停止である。
新しい採取や Lean ビルドは投入していない。

調整役の B4 指示 3 は「保留が出たら止まって報告」。
従ってこちらで open 方針を選んで保留を消したり、main の取り込みを先に行ったりはしない。
指定された代替の A5・Shared の型の照合は §11 に記録済み。
M15・G12 の目的は未達のまま保持し、同じ阻害が三回の連続したゴールターンで
確認されたため、今回ゴールを `blocked` として調整役の方針の更新を待つ。

再開に必要なのは、当該二か所の open 方針が正式な改名表に供給されるか、
調整役からその扱いの明示的な指示を受けること。
再開後は、未採取の残り 10 ファイルを取り込み前に採取し、全 30 本の原文一致と
保留 0 のプレビューを確認してから、main の取り込み・反映・対象ビルド・
小さい公理監査を行う。B4 完了後に M15 の続きへ戻る。

検証済み新規 Lean は 30 ファイル・2,819 行・160 宣言、未検証の下書きは二つのまま。
M10・RHom・完備反射・完備テンソルおよび G12 は完成として扱っていない。

**一覧：済み 9／全体 42（うち追加 0）**。

## 13. B4 再開：恒等 open 方針による保留の解消と main 取り込み（11-14 午後）

調整役の明示指示と main `2be485f04` の `citation-attributes.md` §14 追記により、
§10〜§12 の二つの `DiagramComparison` の open は原文のまま保持する。
使用する四宣言が main に同じ完全名で残ることは調整役が確認済み。
この明示方針により §12 の阻害を解消し、B4 を再開した。
正式な改名表自体は変更せず、ローカルのプレビュー用の表に
`opens[DiagramComparison] = DiagramComparison` の恒等方針を追加した。
原表と適用表の SHA・指示の出所は `approved-opens.json` に保存した。

main 取り込み前に残り 10 ファイルを、指定共有鍵の下で 280 秒上限の組として採取。
既存の 20 本を含め、**全 30 ファイル・19,245 件の参照**がそろった。
全ての採取原文・保存した原文・取り込み前のソースの全バイト一致を確認してから
索引を集約し、承認された方針で全体のプレビューを作った。**保留は 0**。
変更は 15 ファイル、通常 import の移動と参照先の完全名への追従である。
自分のモジュールのファイルパスの移動はない。

その後 `git merge main` を実行し、main `2be485f04` を取り込んだ
（マージコミット `d9a5e6b98`）。取り込み前に作成したプレビューを
`bulk_apply_preview.py` の原文ハッシュ・出力ハッシュ・出力先・プレビュー一致の
検査付きで反映した。削除 0、書き込み先は自分の 15 ファイルのみ。
取り込み後のソースに旧索引で名前解決・再書き換えを行っていない。
反映後の全 30 ファイルがプレビューと全バイト一致することも確認した。

### 13.1 対象ビルドと保存資料

`with_build_lock.sh --class impl --wait 3600` の下で、
自分の 30 モジュールを明示した正規 Lake 対象ビルドを実行し、全て通過した。
二つの `open ...DiagramComparison` を原文のまま残した
`StrictUnderlyingComparison`・`StrictUnderlyingRestriction` も通過した。
公開宣言の名前の一覧は取り込み前と一致する **157 宣言**。
この 157 宣言だけの小さい公理監査を別の共有鍵の組で投入した。
監査の最終結果は次節で記録する。

保存資料は `b4-m15-2026-11-14/` 以下：

- `before-index-complete.json.gz`：取り込み前の全 30 本の採取原文・参照・設定。
- `approved-opens.json`：調整役が承認した恒等 open 方針と改名表の SHA。
- `review-complete.json`：全体プレビューの保留 0。
- `checked-preview-complete.diff.gz`：取り込み前に確認した全差分。
- `approved-apply-bundle.json.gz`：適用した原文・出力ハッシュ付きの束。

§10 の `summary.json`・`review.json` は停止時の履歴として保持している。
現在の保留は解消しており、最新状態はこの §13 と完了時の記録で示す。
未検証の下書き二つは B4 の採取・反映対象の外に保持した。

今回の追従で数学的な宣言は追加していない。
新規 Lean の実測は 30 ファイル・2,819 行・160 宣言（private 3 を含む）のまま。
大きい監査・全体ビルドは実施していない。

**一覧：済み 9／全体 42（うち追加 0）**。

### 13.2 小さい公理監査と B4 の完了

共有鍵の別の組で、公開 **157 宣言**の `#print axioms` を実行し、終了コード 0。
実出力の宣言名の集合・件数が採取した公開宣言の一覧と完全一致した。
依存公理は `propext`・`Classical.choice`・`Quot.sound` のみで、
`sorryAx`・追加公理はない。
この結果と対象ビルド通過により **B4 の追従は完了**。
承認された二つの open は原文を保持したまま検証できた。

最新の完了資料は
[`completion.json`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/completion.json)、
[`audit-declarations.json`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/audit-declarations.json)、
[`audit-public157.txt.gz`](../../../evidence/bhatt-scholze/b4-m15-2026-11-14/audit-public157.txt.gz)。
§10〜§12 は以前の停止と確認の履歴であり、調整役の今回の方針と §13 の検証で
その阻害は解消した。M15・G12 自体の完成とは区別し、ここから M15 の続きへ戻る。

**一覧：済み 9／全体 42（うち追加 0）**。

