# K-L1：∞-S• 構成と連結 K

## 1. 目標・担当範囲

小さい安定 ∞ 圏 C の全 gapped 図式から S•C を構成し、core・実現・loop により連結 K を定義する。
反復 S• による連結スペクトル、加法性、π₀ と三角圏の Grothendieck 群の比較、dg 圏への適用までを証明する。
引用を証明の代用にせず、追加公理・sorry を使わない。条件付き成果を無条件の完成と数えない。

所有：`SerrePositivity/KST/SConstruction/`、namespace `SerrePositivity.KST.SConstruction`。
Core 公開名・型を変更しない。Stable（α-S）、F1 の core（α2）、Spectra（L9）、比較・plus（L2）は読み取り専用。

## 2. 原典・正本

- `k-theory-kst-route.md` §4 D1、§5 K1・K0、§6、§10-5・11・12・13、§13 決定2・5・9・12。
- `foundations.md`。非連結化の最終定義は BGT、暫定実装は Schlichting。非連結化は今回の範囲外。
- `L11-paper.md` §5・11・12・13・S1。特に以下の文言補正を採用する。
- BGT v4 Definition 7.1、Lemma 7.3、Remark 7.4（gapped と第一行）。
- Fiore–Pieper Lemma 4.24、Proposition 4.27、Theorem 4.35、Corollary 3.35（McCarthy 型加法性）。
- HTT 4.3.2.15（相対余極限拡張）、5.1.2.2（関手圏の点ごとの極限・双対）。

## 3. 工程

| 工程 | ファイル | 完了条件 |
| --- | --- | --- |
| L1a | Gapped.lean | Ar[n] と nerve、ihom、零対角・pushout 条件、充満部分単体集合 S_n、単体的関手性 |
| L1b | FirstRow.lean | 第一行制限、相対境界持ち上げ性、trivial Kan fibration |
| L1c | KSpace.lean | 各段の core、対角実現・Kan 置換・Ω、反復 S• と L9 BF スペクトルへの接続 |
| L1d | Additivity.lean | McCarthy 型ホモトピーによる実現後の加法性 |
| L1e | PiZero.lean | π₀ K(C) ≃+ TriangulatedK0(h C)、対象類と自然性 |
| L1f | DGApplication.lean | K(N_dg(Perf_dg D))、dg 関手性、Morita 不変性 |
| L1g | 別途指示 | fibration 定理、filtered 余極限、Bass、非連結化 |

## 4. 設計と実装前の文言

### Ar と gapped

Ar[n] は Fin(n+1) の対 (i,j), i≤j の成分ごとの順序の圏。
単調写像 θ:[m]→[n] は (i,j)↦(θi,θj) を誘導する。
図式圏は ihom(N Ar[n],C)。gapped は全対角 F(i,i) が零対象であり、
i≤j≤k≤l に対する F(i,k)→F(i,l), F(j,k)→F(j,l) の全四角が pushout となる条件。
S_n はこの頂点条件による充満部分単体集合。順序写像による前合成は条件を保つため、
選択を含まず Δᵒᵖ 上の単体的対象を与える。退化する四角にも同じ pushout 条件を課す。

### §10-13：gapped と第一行

原典の結論は Gap([n],C)→Fun(Δ^{1,…,n},C) の ∞ 圏の同値である。
これだけから literal な trivial Kan fibration と結論しない。
要求された元の制限写像について、有限個の相対 cocartesian completion を積み上げ、
零対象と余極限錐の相対境界持ち上げ性から全境界に対する RLP を証明する。
n=0 は零対象の空間として別処理する。全 gapped 図式を保ち、第一行の選択模型に置換しない。
不足する相対拡張補題は本レーン内で証明する。設計変更が必要なら実装前に提案する。
Ar[n] と正方形の積から (0,i),(0,j),(i,i),(i,j) への自然な添字写像を用い、
gapped 図式の全 cofiber 四角形を一つの族として取り出す。
その族は右上角の評価で元の図式を厳密に回収するため、境界上の既存データを保持できる。
相対 cofiber 補完をこの Ar[n] パラメーターに適用する際は、第一行と対角での条件を同時に固定する。
得られる右上角の図式の全四角形が押し出しとなることは、余極限の普遍性と押し出しの貼り合わせから
別に証明する。単に各区間に cofiber を持つことだけで gapped 条件を結論しない。
点ごとの余極限・押し出しを関手 ∞ 圏へ移す向きは、相対始点境界充填と内部 Hom の交換で証明する。
正次元のパラメーター境界では全頂点が指定されているため、境界を厳密に保つ補完の gapped 性は
全部分複体の頂点条件から回収できる。零次元の gapped 性および出力の第一行の厳密な回収は別条件として残す。

### §10-11：加法性

E(A,C,B) の cofiber 列から subobject・quotient への射について、
|core S•E|→|core S•A|×|core S•B| が同値となることを証明する。
E≃A×B という ∞ 圏レベルの誤った主張にはしない。
Fiore–Pieper の McCarthy 型の経路を用い、普遍的 cocartesian completion の制限自明
ファイブレーションでパラメータ付き pushout を選び、単体ホモトピー、単体積版 Quillen A、
対角実現、object/core 比較を証明する。Waldhausen の元の証明からの経路変更を明記する。

### §10-12：最小 fibration 定理（後続 L1g の仕様）

C 安定、D thick、W={f | cofib(f)∈D}。W の2-out-of-3・pushout・extension 安定性が必要。
∞ 局所化と dg 商の比較には mapping 空間の比較まで要求し、H⁰ の Verdier 普遍性で代用しない。
冪等完備化は K₀ を変えるため、連結 K の局所化を全冪等完備 Verdier 列に無条件では課さない。
最終的な非連結 K(D)→K(C)→K((C/D)^idem) の fiber 列へは、必要な cofinality 条件を明示した
連結版と Schlichting suspension を経由する。L11 では ∞ 版全体は未検証である。
今回の L1a–f の成果としてこの定理を完成扱いしない。

### K と界面

L9 の基点・Ω・π_* の座標に従う。BF 模型は単射 ΣX_n→X_(n+1) と、随伴の全基点 π_* 同型。
厳密な Ω 同型を要求しない。未着 API は明示的な入力として隔離し、証明済みの構成と区別する。
π₀ は一般 dg 圏の H⁰D でなく、小さい Perf の H⁰ の TriangulatedK0 と比較する。
S4 未着時は cofiber 列の像が distinguished triangle になる仮定を明記する。
相対 K は L9 のスペクトル fiber を優先し、次数ごとの kernel/cokernel から復元しない。
Kₙ の境界・比較同型は自然性と対象類の式を含む。宇宙は S1.1 に従い小さい模型にそろえる。

## 5. 検証・保存

各保存単位で `lake build SerrePositivity.KST.SConstruction` と
`lake env lean scripts/audit_kst_s_construction.lean` を実行する。
公開宣言を #check / #print axioms で監査し、許可するのは propext、Classical.choice、Quot.sound のみ。
全体ビルドは工程の区切りで行う。自分の import 閉包外の並行作業の失敗は記録して続ける。
自分の検証済みファイルだけを保存し、経緯はコミットメッセージに記す。

## 6. 現在地・主要宣言

L1a 完了。対象ビルド 1932 jobs、公理監査 26 宣言（標準3公理のみ）。

以下で `C : SSet.{u}`、`m,n,l : ℕ`。`Ar n : Type u` は成分ごとの順序圏。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `arNerve` | `(n : ℕ) → SSet.{u}` |
| `arMap` | `(Fin (m+1) →o Fin (n+1)) → (Ar m →o Ar n)` |
| `arNerveMap` | `(θ : Fin (m+1) →o Fin (n+1)) → (arNerve m ⟶ arNerve n)` |
| `diagramSpace` | `(n : ℕ) → (C : SSet.{u}) → SSet.{u}`、値は `(ihom (arNerve n)).obj C` |
| `IsGapped` | `(F : arNerve n ⟶ C) → Prop`、零対角かつ i≤j≤k≤l の全四角形が押し出し |
| `IsGapped.precomp` | `IsGapped F → (θ : Fin (m+1) →o Fin (n+1)) → IsGapped (arNerveMap θ ≫ F)` |
| `gappedSubcomplex` | `(n : ℕ) → (C : SSet.{u}) → (diagramSpace n C).Subcomplex` |
| `sConstruction` | `(n : ℕ) → (C : SSet.{u}) → SSet.{u}` |
| `sConstruction_quasicategory` | `[Quasicategory C] → Quasicategory (sConstruction n C)` |
| `sMap` | `(C : SSet.{u}) → (θ : Fin (m+1) →o Fin (n+1)) → (sConstruction n C ⟶ sConstruction m C)` |
| `sMap_id` | `sMap C OrderHom.id = 𝟙 (sConstruction n C)` |
| `sMap_comp` | `sMap C (φ.comp θ) = sMap C φ ≫ sMap C θ` |
| `simplicialSConstruction` | `(C : SSet.{u}) → (SimplexCategoryᵒᵖ ⥤ SSet.{u})` |

補助公開宣言は `arObj`、Ar/nerve の恒等・合成則、`intervalStep` と上下界、
`arSquareOrder`、`arSquare`、`arSquare_naturality`、`sMap_ι`。全26宣言の展開された型を監査スクリプトで検査する。
上記は定義・関手法則であり安定性を仮定しない。quasicategory instance だけは明記した前提を持つ。

L1b 進行中。第一行制限と零対角の補完段階を実装済み。対象ビルド2040 jobs、累計218宣言の監査（標準3公理のみ）。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `firstRowNerve` | `(n : ℕ) → SSet.{u}`、`nerve (ULift (Fin n))` |
| `firstRowRestriction` | `(n : ℕ) → (C : SSet.{u}) → (sConstruction n C ⟶ (ihom (firstRowNerve n)).obj C)` |
| `firstRowSimplexIso` | `(n : ℕ) → ((Δ[n] : SSet.{u}) ≅ firstRowNerve (n+1))` |
| `gappedDiagram` | `(v : (sConstruction n C) _⦋0⦌) → (arNerve n ⟶ C)` |
| `gappedDiagram_isGapped` | `(v : (sConstruction n C) _⦋0⦌) → IsGapped (gappedDiagram v)` |
| `zeroChoices` | `(C : SSet.{u}) → C.Subcomplex`、全零対象の充満部分複体 |
| `zeroChoices_isContractibleKan` | `(C : SSet.{u}) → [HasZeroVertex C] → IsContractibleKan (zeroChoices C : SSet.{u})` |
| `exists_zeroChoices_extension` | `[HasZeroVertex C] → (i : A ⟶ B) → [Mono i] → (f : A ⟶ (zeroChoices C : SSet.{u})) → ∃ F, i ≫ F = f` |
| `zeroFrameDiagrams` | `(n : ℕ) → (C : SSet.{u}) → SSet.{u}`、`frameNerve n` の全図式のうち全対角が零対象となる充満部分複体 |
| `zeroFrameProjection` | `(n : ℕ) → (C : SSet.{u}) → (zeroFrameDiagrams n C ⟶ (ihom (framePositiveRow n : SSet.{u})).obj C)` |
| `zeroFrameProjection_trivialKanFibration` | `(n : ℕ) → (C : SSet.{u}) → [HasZeroVertex C] → TrivialKanFibration (zeroFrameProjection n C)` |

`FrameAr n` は Ar[n] の「左端0または対角」の順序部分型、`frameNerve n` はその nerve、
`framePositiveRow n` は対角(0,0)を除く第一行の全部分複体。
`frameChain_diagonal_endpoint`・`frameNerve_diagonal_endpoint` は、その第一行の順序凸性と、
新しい鎖がどちらかの端点に対角を持つことを証明する。
`exists_extension_of_initial_or_terminal_endpoints`、`frame_extend_boundary`、
`exists_extension_with_vertices`、`zeroFrame_extend_boundary` は相対拡張の補助定理。
全公開宣言の展開された型・前提を監査スクリプトで検査する。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `frameFirstRowIso` | `(n : ℕ) → (firstRowNerve.{u} n ≅ (framePositiveRow n : SSet.{u}))` |
| `frameInclusion` | `(n : ℕ) → (frameNerve.{u} n ⟶ arNerve n)` |
| `gappedFrameRestriction` | `(n : ℕ) → (C : SSet.{u}) → (sConstruction n C ⟶ zeroFrameDiagrams n C)` |
| `frameRowRestriction` | `(n : ℕ) → (C : SSet.{u}) → (zeroFrameDiagrams n C ⟶ (ihom (firstRowNerve n)).obj C)` |
| `firstRowRestriction_factor` | `gappedFrameRestriction n C ≫ frameRowRestriction n C = firstRowRestriction n C` |
| `frameRowRestriction_trivialKanFibration` | `(n : ℕ) → (C : SSet.{u}) → [HasZeroVertex C] → TrivialKanFibration (frameRowRestriction n C)` |
| `gappedCofiberTriangle` | `(hF : IsGapped F) → (i j k : Fin (n+1)) → (hij : i ≤ j) → (hjk : j ≤ k) → ZeroTriangle C` |
| `gappedCofiberTriangle_isCofiber` | `(hF : IsGapped F) → (i j k : Fin (n+1)) → (hij : i ≤ j) → (hjk : j ≤ k) → IsCofiberSequence (gappedCofiberTriangle hF i j k hij hjk)` |

第一行の二表示を同型で接続し、元の制限を厳密に因子分解した。
原典 [BGT v4 p.44](https://arxiv.org/pdf/1001.2282v4#page=44) Definition 7.1 の原始条件は三つ組の cofiber 四角形である。
本実装の全四つ組の押し出し条件から原典の三つ組を取り出す向きは `gappedCofiberTriangle_isCofiber` で証明済み。
逆向きの全四つ組への押し出し貼り合わせは、cofiber 補完段階の未完了範囲に含む。

零対角の射影の trivial Kan fibration は無条件の相対境界証明であり、quasicategory 性・安定性を仮定しない。
cofiber 一段の補完について次を実装した。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `pushoutDiagrams` | `(C : SSet.{u}) → SSet.{u}`、押し出し四角形の全部分複体 |
| `pushoutDiagramsCoconesIso` | `(C : SSet.{u}) → [Quasicategory C] → (pushoutDiagrams C ≅ colimitCocones (horn 2 0) C)` |
| `pushoutProjection` | `(C : SSet.{u}) → (pushoutDiagrams C ⟶ (ihom (horn 2 0)).obj C)` |
| `pushoutProjection_hasLiftingProperty_boundary` | `(C : SSet.{u}) → [Quasicategory C] → (n : ℕ) → HasLiftingProperty (boundary (n+1)).ι (pushoutProjection C)` |
| `cofiberDiagrams` | `(C : SSet.{u}) → SSet.{u}`、零角 (0,1) を持つ押し出し四角形の全部分複体 |
| `cofiberProjection` | `(C : SSet.{u}) → (cofiberDiagrams C ⟶ (ihom (Δ[1] : SSet.{u})).obj C)` |
| `cofiberProjection_trivialKanFibration` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → TrivialKanFibration (cofiberProjection C)` |
| `exists_relative_cofiberFamily` | `[Quasicategory C] → [IsStable C] → (i : A ⟶ B) → [Mono i] → (d : B ⟶ (ihom Δ[1]).obj C) → (a : A ⟶ cofiberDiagrams C) → (a ≫ cofiberProjection C = i ≫ d) → ∃ F, i ≫ F = a ∧ F ≫ cofiberProjection C = d` |
| `cofiberFamilySpace` | `(d : A ⟶ (ihom (Δ[1] : SSet.{u})).obj C) → SSet.{u}`、後合成の fiber |
| `cofiberFamilySpace_isContractibleKan` | `[Quasicategory C] → [IsStable C] → (d : A ⟶ (ihom Δ[1]).obj C) → IsContractibleKan (cofiberFamilySpace d)` |
| `cofiberFamiliesIso` | `[Quasicategory C] → [IsStable C] → (d : A ⟶ (ihom Δ[1]).obj C) → (F G : A ⟶ cofiberDiagrams C) → (F ≫ cofiberProjection C = d) → (G ≫ cofiberProjection C = d) → FunctorIso F G` |
| `cofiberSection` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → ((ihom Δ[1]).obj C ⟶ cofiberDiagrams C)` |
| `cofiberSection_projection` | `cofiberSection C ≫ cofiberProjection C = 𝟙 _` |
| `cofiberFunctor` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → ((ihom Δ[1]).obj C ⟶ C)`、選んだ四角形の (1,1) での評価 |

`exists_relative_colimitCoconeFamily`・`exists_relative_pushoutFamily` は、各入力図式の余極限が存在する場合に、任意の単射に沿う相対補完を与える。
cofiber の射影の零次元には `IsStable.cofiber_exists`、正次元には零対象へ向かう辺の射影と
普遍押し出しの射影の正次元境界 RLP を用いた。追加の cofiber 存在公理は使っていない。

Ar[n] 全体への適用をつなぐ自然な cofiber 抽出を実装した。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `arCofiberSquareMap` | `(n : ℕ) → (arNerve.{u} n ⊗ (Δ[1] ⊗ Δ[1]) ⟶ arNerve n)` |
| `arCofiberFamily` | `(F : arNerve n ⟶ C) → (arNerve n ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C)` |
| `gappedCofiberFamily` | `(hF : IsGapped F) → (arNerve n ⟶ cofiberDiagrams C)` |
| `cofiberApex` | `(C : SSet.{u}) → (cofiberDiagrams C ⟶ C)` |
| `gappedCofiberFamily_apex` | `(hF : IsGapped F) → gappedCofiberFamily hF ≫ cofiberApex C = F` |
| `arCofiberFamilyOperator` | `(n : ℕ) → (C : SSet.{u}) → ((ihom (arNerve n)).obj C ⟶ (ihom (arNerve n)).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C))` |
| `gappedCofiberFamiliesMap` | `(n : ℕ) → (C : SSet.{u}) → (sConstruction n C ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C))` |
| `gappedCofiberFamiliesMap_apex` | `gappedCofiberFamiliesMap n C ≫ (ihom (arNerve n)).map (cofiberApex C) = (gappedSubcomplex n C).ι` |

これらの抽出・右上角の回収の宣言には quasicategory 性も安定性も要求しない。
内部 currying と全部分複体を標的とする内部 Hom の同型により、頂点ごとの抽出を
全てのパラメーターに自然な単体集合の射にした。

点ごとの余極限の関手圏への移送と、枠からの相対補完を接続した。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `evaluateFunctorCocone` | `(c : JoinCocone p) → (k : K _⦋0⦌) → JoinCocone (evaluateFunctorDiagram p k)`、`p : J ⟶ (ihom K).obj X` |
| `IsPointwiseColimitCone` | `(c : JoinCocone p) → Prop`、全 k で `IsColimitCone (evaluateFunctorCocone c k)` |
| `isColimitCone_of_pointwise` | `[Quasicategory X] → (c : JoinCocone p) → IsPointwiseColimitCone c → IsColimitCone c` |
| `isPushoutSquare_of_pointwise` | `[Quasicategory X] → (F : Δ[1] ⊗ Δ[1] ⟶ (ihom K).obj X) → (∀ k, IsPushoutSquare (F ≫ evaluateFunctorAt k)) → IsPushoutSquare F` |
| `isZeroVertex_functorVertex_of_pointwise` | `(f : K ⟶ X) → (∀ k, IsZeroVertex (f.app (Opposite.op ⦋0⦌) k)) → IsZeroVertex (functorVertex f)`、quasicategory 性不要 |
| `cofiberFamilyTriangle` | `(H : A ⟶ cofiberDiagrams C) → ZeroTriangle ((ihom A).obj C)` |
| `cofiberFamilyTriangle_isCofiber` | `[Quasicategory C] → (H : A ⟶ cofiberDiagrams C) → IsCofiberSequence (cofiberFamilyTriangle H)` |
| `frameCofiberInputs` | `(n : ℕ) → (C : SSet.{u}) → (zeroFrameDiagrams n C ⟶ (ihom (arNerve n)).obj ((ihom Δ[1]).obj C))` |
| `gappedCofiberFamiliesMap_input` | `gappedCofiberFamiliesMap n C ≫ (ihom (arNerve n)).map (cofiberProjection C) = gappedFrameRestriction n C ≫ frameCofiberInputs n C` |
| `ArCofiberCompletion` | `(n : ℕ) → (i : A ⟶ B) → (a : A ⟶ sConstruction n C) → (b : B ⟶ zeroFrameDiagrams n C) → Type u`。実際の cofiber 族と入力・境界の等号を保持する |
| `arCofiberCompletion` | `[Quasicategory C] → [IsStable C] → (n : ℕ) → (i : A ⟶ B) → [Mono i] → (a : A ⟶ sConstruction n C) → (b : B ⟶ zeroFrameDiagrams n C) → (a ≫ gappedFrameRestriction n C = i ≫ b) → ArCofiberCompletion n i a b` |
| `ArCofiberCompletion.diagram_boundary` | `(c : ArCofiberCompletion n i a b) → i ≫ c.diagram = a ≫ (gappedSubcomplex n C).ι` |
| `FirstRowCofiberData` | `(n : ℕ) → (i : A ⟶ B) → (a : A ⟶ sConstruction n C) → (d : B ⟶ (ihom (firstRowNerve n)).obj C) → Type u`。枠とその第一行・境界の等号と `ArCofiberCompletion` を保持する |
| `firstRowCofiberData` | `[Quasicategory C] → [IsStable C] → (n : ℕ) → (i : A ⟶ B) → [Mono i] → (a : A ⟶ sConstruction n C) → (d : B ⟶ (ihom (firstRowNerve n)).obj C) → (a ≫ firstRowRestriction n C = i ≫ d) → FirstRowCofiberData n i a d` |
| `FirstRowCofiberData.toGapped` | `(c : FirstRowCofiberData n i a d) → Function.Surjective (i.app (Opposite.op ⦋0⦌)) → (B ⟶ sConstruction n C)` |
| `FirstRowCofiberData.toGapped_boundary` | `(c : FirstRowCofiberData n i a d) → (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) → i ≫ c.toGapped hi = a` |

構造体の型・コンストラクタ・明示的なフィールドも監査対象に含めた。
`exists_gappedBoundaryFilling_of_firstRowFilling` は `[Quasicategory C] [IsStable C]` の下で
`a : boundary (r+1) ⟶ sConstruction n C`、`d : Δ[r+1] ⟶ (ihom (firstRowNerve n)).obj C`、
`h : a ≫ firstRowRestriction n C = (boundary (r+1)).ι ≫ d` から
`∃ F : Δ[r+1] ⟶ sConstruction n C, (boundary (r+1)).ι ≫ F = a` を証明する。
この結論は **F の第一行が d と等しいことを含まない**。したがってこれを RLP の完成と数えない。

恒等辺を持つ押し出しと、零対角の枠で固定する cofiber 族を証明した。
下表で `Square := (Δ[1] ⊗ Δ[1] : SSet.{u})`、`K,C : SSet.{u}`。
これらは枠での実際の図式を保つ構成であり、第一行を別の同値な模型に置き換えていない。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `isInitialVertex_pointCoslice_of_isInvertibleEdge` | `[Quasicategory C] → (a : Δ[0] ⟶ C) → (t : (sliceUnder a) _⦋0⦌) → IsInvertibleEdge (pointCosliceVertexEdge a t) → IsInitialVertex t` |
| `identityCocone` | `(a : Δ[0] ⟶ C) → JoinCocone a` |
| `identityCocone_isColimit` | `[Quasicategory C] → (a : Δ[0] ⟶ C) → IsColimitCone (identityCocone a)` |
| `isColimitCone_iff_of_map_eq` | `{p q : K ⟶ C} → (c : JoinCocone p) → (d : JoinCocone q) → c.val = d.val → (IsColimitCone c ↔ IsColimitCone d)` |
| `identityCocone_val` | `(a : Δ[0] ⟶ C) → (identityCocone a).val = SSet.const (SSet.yonedaEquiv a)` |
| `pointCocone_isColimit_of_constant` | `[Quasicategory C] → {p : Δ[0] ⟶ C} → (c : JoinCocone p) → (x : C _⦋0⦌) → c.val = SSet.const x → IsColimitCone c` |
| `lastVertex_rightAnodyne` | `rightAnodyneExtensions (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1])` |
| `edgeTargetShape` | `join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1]` |
| `edgeTargetCocone` | `(F : (Δ[1] : SSet.{u}) ⟶ C) → JoinCocone F` |
| `edgeTargetCocone_isColimit` | `[Quasicategory C] → (F : (Δ[1] : SSet.{u}) ⟶ C) → IsColimitCone (edgeTargetCocone F)` |
| `isPushoutSquare_fst` | `[Quasicategory C] → (F : (Δ[1] : SSet.{u}) ⟶ C) → IsPushoutSquare (CartesianMonoidalCategory.fst _ _ ≫ F)` |
| `isPushoutSquare_snd` | `[Quasicategory C] → (F : (Δ[1] : SSet.{u}) ⟶ C) → IsPushoutSquare (CartesianMonoidalCategory.snd _ _ ≫ F)` |
| `frameCofiberSquareOrder` | `(n : ℕ) → (FrameAr.{u} n × ULift.{u} (Fin 2 × Fin 2) →o FrameAr.{u} n)` |
| `frameCofiberSquareMap` | `(n : ℕ) → (frameNerve.{u} n ⊗ Square ⟶ frameNerve n)` |
| `frameCofiberSquareMap_inclusion` | `(n : ℕ) → frameCofiberSquareMap n ≫ frameInclusion n = (frameInclusion n ▷ Square) ≫ arCofiberSquareMap n` |
| `frameCofiberSquareAt` | `(a : FrameAr.{u} n) → (Square ⟶ frameNerve n)` |
| `frameCofiberSquareAt_firstRow` | `(a : FrameAr.{u} n) → a.val.down.val.1 = 0 → frameCofiberSquareAt a = CartesianMonoidalCategory.fst _ _ ≫ squareBottomEdge ≫ frameCofiberSquareAt a` |
| `frameCofiberSquareAt_diagonal` | `(a : FrameAr.{u} n) → IsDiagonal a.val → frameCofiberSquareAt a = CartesianMonoidalCategory.snd _ _ ≫ squareLeftEdge ≫ frameCofiberSquareAt a` |
| `frameCofiberSquareAt_isPushout` | `[Quasicategory C] → (F : frameNerve n ⟶ C) → (a : FrameAr.{u} n) → IsPushoutSquare (frameCofiberSquareAt a ≫ F)` |
| `frameCofiberFamily` | `(F : frameNerve n ⟶ C) → (frameNerve n ⟶ (ihom Square).obj C)` |
| `zeroFrameCofiberFamily` | `[Quasicategory C] → (F : frameNerve n ⟶ C) → IsZeroFrameVertex (functorVertex F) → (frameNerve n ⟶ cofiberDiagrams C)` |
| `zeroFrameCofiberFamily_ι` | `[Quasicategory C] → (F : frameNerve n ⟶ C) → (hF : IsZeroFrameVertex (functorVertex F)) → zeroFrameCofiberFamily F hF ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι = frameCofiberFamily F` |
| `zeroFrameCofiberFamily_apex` | `[Quasicategory C] → (F : frameNerve n ⟶ C) → (hF : IsZeroFrameVertex (functorVertex F)) → zeroFrameCofiberFamily F hF ≫ cofiberApex C = F` |

補助宣言 `horn_one_one_eq_last_face`・`edgeTargetShape_inl`・`edgeTargetShape_restrict_last`、
`identityLegAttachment_isPushout`・`identityFirstLegAttachment_isPushout`、
`isColimitCone_iff_restrict_of_identity_leg`・`isColimitCone_iff_restrict_of_identity_first_leg`、
`spanCoconeSquare_fst_restrict`・`spanCoconeSquare_snd_restrict`、
`arCofiberSquareOrder_mem_frame`・`frameCofiberFamily_vertex`・`frameCofiberSquareAt_zero_corner`・
`frameCofiberSquareMap_apex`・`frameCofiberFamily_apex` も正確な型と公理を監査した。
α-S の `ColimitAttachment` の普遍性を読み取り専用で用いている。
枠の cofiber 族とその厳密な回収に `IsStable C` は必要なく、`Quasicategory C` だけを使う。
恒等脚の条件を除去したり、h C の通常の押し出しで代用したりしていない。

**未完了**：この枠上の族と指定境界の族を合わせた相対 cofiber 補完、
出力図式の第一行が指定入力と厳密に一致する等号、零次元で作る図式の gapped 条件、
三つ組の cofiber 条件から全四つ組の押し出しへの貼り合わせ。
`firstRowRestriction` の trivial Kan fibration と L1b 全体はまだ完了していない。
L1c–f は未着手。L1g は別途指示待ち。
