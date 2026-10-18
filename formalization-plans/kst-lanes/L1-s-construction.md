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

L1b 進行中。第一行制限と零対角の補完段階を実装済み。対象ビルド2085 jobs、累計344宣言の監査（標準3公理のみ）。

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
逆向きの全四つ組への押し出し貼り合わせは、後掲の `isGapped_iff_triples` で証明済み。

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

枠の cofiber 族をパラメーターに自然な射にし、指定境界と枠を同時に保つ補完を構成した。
その結果、第一行制限の **正次元の全境界に対する RLP** が厳密な両側の等号を伴って証明済み。
以下で `ιFrame := (fullSubcomplexOnVertices _ IsZeroFrameVertex).ι`、
`ιCof := (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι` と書く。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `frameCofiberFamilyOperator` | `(n : ℕ) → (C : SSet.{u}) → ((ihom (frameNerve n)).obj C ⟶ (ihom (frameNerve n)).obj ((ihom Square).obj C))` |
| `frameCofiberFamilyOperator_vertex` | `(F : frameNerve n ⟶ C) → (frameCofiberFamilyOperator n C).app (Opposite.op ⦋0⦌) (functorVertex F) = functorVertex (frameCofiberFamily F)` |
| `IsZeroFrameVertex.frameCofiberFamily_vertex` | `[Quasicategory C] → {F : frameNerve n ⟶ C} → IsZeroFrameVertex (functorVertex F) → (a : (frameNerve n) _⦋0⦌) → IsCofiberDiagramVertex ((frameCofiberFamily F).app (Opposite.op ⦋0⦌) a)` |
| `zeroFrameCofiberFamiliesMap` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → (zeroFrameDiagrams n C ⟶ (ihom (frameNerve n)).obj (cofiberDiagrams C))` |
| `zeroFrameCofiberFamiliesMap_ι` | `[Quasicategory C] → zeroFrameCofiberFamiliesMap n C ≫ (ihom (frameNerve n)).map ιCof = ιFrame ≫ frameCofiberFamilyOperator n C` |
| `frameCofiberFamilyOperator_apex` | `frameCofiberFamilyOperator n C ≫ (ihom (frameNerve n)).map (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = 𝟙 _` |
| `zeroFrameCofiberFamiliesMap_apex` | `[Quasicategory C] → zeroFrameCofiberFamiliesMap n C ≫ (ihom (frameNerve n)).map (cofiberApex C) = ιFrame` |
| `ihomCurry_pre_whiskerLeft` | `(f : A ⟶ B) → (K X : SSet.{u}) → (pre (K ◁ f)).app X ≫ (ihomCurryIso K A X).hom = (ihomCurryIso K B X).hom ≫ (pre f).app ((ihom K).obj X)` |
| `arCofiberFamilyOperator_frame` | `arCofiberFamilyOperator n C ≫ (pre (frameInclusion n)).app ((ihom Square).obj C) = (pre (frameInclusion n)).app C ≫ frameCofiberFamilyOperator n C` |
| `gappedCofiberFamiliesMap_frame` | `[Quasicategory C] → gappedCofiberFamiliesMap n C ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = gappedFrameRestriction n C ≫ zeroFrameCofiberFamiliesMap n C` |
| `frameCofiberSquareMap_bottom` | `(n : ℕ) → (frameNerve n ◁ squareBottomEdge) ≫ frameCofiberSquareMap n = (frameInclusion n ▷ (Δ[1] : SSet.{u})) ≫ arCofiberInputMap n` |
| `frameCofiberFamilyOperator_input` | `frameCofiberFamilyOperator n C ≫ (ihom (frameNerve n)).map ((pre squareBottomEdge).app C) = frameCofiberInputOperator n C ≫ (pre (frameInclusion n)).app ((ihom (Δ[1] : SSet.{u})).obj C)` |
| `zeroFrameCofiberFamiliesMap_input` | `[Quasicategory C] → zeroFrameCofiberFamiliesMap n C ≫ (ihom (frameNerve n)).map (cofiberProjection C) = frameCofiberInputs n C ≫ (pre (frameInclusion n)).app ((ihom (Δ[1] : SSet.{u})).obj C)` |
| `frameInclusion_mono` | `(n : ℕ) → Mono (frameInclusion.{u} n)` |
| `exists_arCofiberCompletion_preserving_frame` | `[Quasicategory C] → [IsStable C] → (n : ℕ) → (i : A ⟶ B) → [Mono i] → (a : A ⟶ sConstruction n C) → (b : B ⟶ zeroFrameDiagrams n C) → (a ≫ gappedFrameRestriction n C = i ≫ b) → ∃ c : ArCofiberCompletion n i a b, c.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = b ≫ zeroFrameCofiberFamiliesMap n C` |
| `ArCofiberCompletion.diagram_frame` | `[Quasicategory C] → (c : ArCofiberCompletion n i a b) → (c.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = b ≫ zeroFrameCofiberFamiliesMap n C) → c.diagram ≫ (pre (frameInclusion n)).app C = b ≫ ιFrame` |
| `exists_firstRowCofiberData_preserving_frame` | `[Quasicategory C] → [IsStable C] → (n : ℕ) → (i : A ⟶ B) → [Mono i] → (a : A ⟶ sConstruction n C) → (d : B ⟶ (ihom (firstRowNerve n)).obj C) → (a ≫ firstRowRestriction n C = i ≫ d) → ∃ c : FirstRowCofiberData n i a d, c.cofibers.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = c.frame ≫ zeroFrameCofiberFamiliesMap n C` |
| `FirstRowCofiberData.toGapped_frame` | `[Quasicategory C] → (c : FirstRowCofiberData n i a d) → (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) → (c.cofibers.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = c.frame ≫ zeroFrameCofiberFamiliesMap n C) → c.toGapped hi ≫ gappedFrameRestriction n C = c.frame` |
| `FirstRowCofiberData.toGapped_firstRow` | 同じ c・hi・枠保持の前提から `c.toGapped hi ≫ firstRowRestriction n C = d` |
| `firstRowRestriction_hasLiftingProperty_of_vertexSurjective` | `[Quasicategory C] → [IsStable C] → (n : ℕ) → (i : A ⟶ B) → [Mono i] → Function.Surjective (i.app (Opposite.op ⦋0⦌)) → HasLiftingProperty i (firstRowRestriction n C)` |
| `firstRowRestriction_hasLiftingProperty_boundary` | `(n r : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → HasLiftingProperty (boundary (r+1)).ι (firstRowRestriction n C)` |

未証明の枠保持条件を構造体に追加したのではなく、相対内部 Hom の
`trivialKanFibration_pullbackObjObjπ` から実際の補完を構成した。
従来の第一行の等号を含まない充填補題より強く、任意の単射 i が全頂点を含む場合に
指定した第一行と境界の両方を厳密に保つ。

三つ組から全四つ組への還元と、任意の第一行に対する零対角 Ar[n] 図式の構成を証明した。
α-S の押し出し貼り合わせ `isPushoutSquare_pasting_cancel_left` を読み取り専用で使用した。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `intervalTriple` | `(a b c : Fin (n+1)) → (a ≤ b) → (b ≤ c) → (Fin 3 →o Fin (n+1))` |
| `arCofiberRectangleOrder` | `(i j k l : Fin (n+1)) → (i ≤ j) → (j ≤ k) → (k ≤ l) → (ULift.{u} (Fin 3 × Fin 2) →o Ar.{u} n)` |
| `arCofiberRectangle` | `(i j k l : Fin (n+1)) → (i ≤ j) → (j ≤ k) → (k ≤ l) → ((Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n)` |
| `arCofiberRectangle_left` | `(i j k l : Fin (n+1)) → (hij : i ≤ j) → (hjk : j ≤ k) → (hkl : k ≤ l) → pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 2 = arSquare i j j k hij le_rfl hjk` |
| `arCofiberRectangle_outer` | 同じ i,j,k,l,hij,hjk,hkl について `pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 1 = arSquare i j j l hij le_rfl (hjk.trans hkl)` |
| `arCofiberRectangle_right` | 同じ i,j,k,l,hij,hjk,hkl について `pastingSquare (arCofiberRectangle i j k l hij hjk hkl) 0 = arSquare i j k l hij hjk hkl` |
| `arSquares_isPushout_of_triples` | `[Quasicategory C] → (F : arNerve n ⟶ C) → (∀ (i j k : Fin (n+1)) (hij : i ≤ j) (hjk : j ≤ k), IsPushoutSquare (arSquare i j j k hij le_rfl hjk ≫ F)) → ∀ (i j k l : Fin (n+1)) (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l), IsPushoutSquare (arSquare i j k l hij hjk hkl ≫ F)` |
| `isGapped_iff_triples` | `[Quasicategory C] → (F : arNerve n ⟶ C) → (IsGapped F ↔ (∀ j : Fin (n+1), IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj j j le_rfl)))) ∧ (∀ (i j k : Fin (n+1)) (hij : i ≤ j) (hjk : j ≤ k), IsPushoutSquare (arSquare i j j k hij le_rfl hjk ≫ F)))` |
| `ArCofiberCompletion.diagram_zero_diagonal` | `[Quasicategory C] → (c : ArCofiberCompletion n i a b) → (c.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = b ≫ zeroFrameCofiberFamiliesMap n C) → (v : B _⦋0⦌) → (j : Fin (n+1)) → IsZeroVertex (((functorVertexEquiv (arNerve n) C).symm (c.diagram.app (Opposite.op ⦋0⦌) v)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj j j le_rfl)))` |
| `FirstRowCofiberData.diagram_firstRow` | `[Quasicategory C] → (c : FirstRowCofiberData n i a d) → (c.cofibers.family ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = c.frame ≫ zeroFrameCofiberFamiliesMap n C) → c.diagram ≫ (pre (firstRowInclusion n)).app C = d` |
| `exists_firstRowDiagramWithZeroDiagonal` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → (p : firstRowNerve n ⟶ C) → ∃ F : arNerve n ⟶ C, firstRowInclusion n ≫ F = p ∧ ∀ j : Fin (n+1), IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj j j le_rfl)))` |

三つ組の正方形を左側 `(i,j,j,k)` と外側 `(i,j,j,l)` に置く長方形を実際の
`Δ[2] ⊗ Δ[1] ⟶ arNerve n` として構成し、右側の `(i,j,k,l)` に相殺を適用した。
この還元に安定性や零対角の仮定は不要で、`isGapped_iff_triples` では零対角を別に保持する。
また空の指定境界に枠を保つ補完を適用し、任意の第一行から実際の Ar[n] 図式を構成した。
この存在定理の結論に三つ組の押し出し性は含まれておらず、L1b 完成とは数えない。

関手圏の余極限について、点ごとの存在から自然な余錐を構成する向きと、
任意の余極限余錐を評価へ戻す向きを接続した。
これは構成済みの cofiber 族の普遍性を部分図式へ制限するための API である。
既存の Core A6 の公開宣言は変更していない。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `HasPointwiseColimits` | `(p : J ⟶ (ihom K).obj X) → Prop`、定義は `∀ k : K _⦋0⦌, HasColimit (evaluateFunctorDiagram p k)` |
| `IsPointwiseColimitCone.hasPointwiseColimits` | `{c : JoinCocone p} → IsPointwiseColimitCone c → HasPointwiseColimits p` |
| `exists_pointwiseColimitCone` | `[Quasicategory X] → (p : J ⟶ (ihom K).obj X) → HasPointwiseColimits p → ∃ c : JoinCocone p, IsPointwiseColimitCone c` |
| `hasColimit_of_hasPointwiseColimits` | `[Quasicategory X] → (p : J ⟶ (ihom K).obj X) → HasPointwiseColimits p → HasColimit p` |
| `IsPointwiseColimitCone.of_vertexIso` | `[Quasicategory X] → {c d : JoinCocone p} → IsPointwiseColimitCone c → VertexIso (X := sliceUnder p) c d → IsPointwiseColimitCone d` |
| `isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits` | `[Quasicategory X] → HasPointwiseColimits p → (c : JoinCocone p) → IsColimitCone c → IsPointwiseColimitCone c` |
| `isColimitCone_iff_pointwise_of_hasPointwiseColimits` | `[Quasicategory X] → HasPointwiseColimits p → (c : JoinCocone p) → (IsColimitCone c ↔ IsPointwiseColimitCone c)` |
| `isPushoutSquare_iff_pointwise_of_hasPointwiseColimits` | `[Quasicategory X] → (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom K).obj X) → HasPointwiseColimits (pushoutSpan F) → (IsPushoutSquare F ↔ ∀ k : K _⦋0⦌, IsPushoutSquare (F ≫ evaluateFunctorAt k))` |
| `reindexFunctorCocone` | `(c : JoinCocone p) → (f : L ⟶ K) → JoinCocone (p ≫ (pre f).app X)`、`p : J ⟶ (ihom K).obj X` |
| `IsPointwiseColimitCone.reindex` | `{c : JoinCocone p} → IsPointwiseColimitCone c → (f : L ⟶ K) → IsPointwiseColimitCone (reindexFunctorCocone c f)` |
| `isColimitCone_reindex_of_hasPointwiseColimits` | `[Quasicategory X] → HasPointwiseColimits p → (c : JoinCocone p) → IsColimitCone c → (f : L ⟶ K) → IsColimitCone (reindexFunctorCocone c f)` |

`exists_pointwiseColimitCone` は α-S の `exists_colimitCoconeFamily` により図式の転置に沿って
普遍余錐を coherent に選び、内部 Hom を再び転置して実際の余錐を作る。
逆方向はこの余錐と任意の普遍余錐を coslice の同型で比較して証明した。
点ごとの存在前提を落とした逆方向や、余極限の交換そのものを無条件で主張していない。
添字の前合成 f には単射性も quasicategory 性も要求しない。

S• の零図式と次数0・1の第一行制限を完成した。
以下で `X : SSet.{u}`、`P : X _⦋0⦌ → Prop`、`Square := (Δ[1] ⊗ Δ[1] : SSet.{u})`。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `fullSubcomplex_hasLiftingProperty_of_vertexSurjective` | `(P : X _⦋0⦌ → Prop) → (i : A ⟶ B) → Function.Surjective (i.app (Opposite.op ⦋0⦌)) → HasLiftingProperty i (fullSubcomplexOnVertices X P).ι` |
| `isInitialVertex_fullSubcomplex_of_ambient` | `(P : X _⦋0⦌ → Prop) → (v : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌) → IsInitialVertex v.val → IsInitialVertex v` |
| `isTerminalVertex_fullSubcomplex_of_ambient` | 同じ P・v に対し `IsTerminalVertex v.val → IsTerminalVertex v` |
| `isGapped_const` | `(n : ℕ) → [Quasicategory C] → (z : C _⦋0⦌) → IsZeroVertex z → IsGapped (SSet.const z : arNerve n ⟶ C)` |
| `sConstructionZeroVertex` | `(n : ℕ) → [Quasicategory C] → (z : C _⦋0⦌) → IsZeroVertex z → (sConstruction n C) _⦋0⦌` |
| `sConstructionZeroVertex_isZero` | `(n : ℕ) → [Quasicategory C] → (z : C _⦋0⦌) → (hz : IsZeroVertex z) → IsZeroVertex (sConstructionZeroVertex n z hz)` |
| `sMap_zeroVertex` | `[Quasicategory C] → (θ : Fin (m+1) →o Fin (n+1)) → (z : C _⦋0⦌) → (hz : IsZeroVertex z) → (sMap C θ).app (Opposite.op ⦋0⦌) (sConstructionZeroVertex n z hz) = sConstructionZeroVertex m z hz` |
| `sConstruction_hasZeroVertex` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [HasZeroVertex C] → HasZeroVertex (sConstruction n C)` |
| `sConstructionZero_isZeroVertex` | `(C : SSet.{u}) → [Quasicategory C] → (v : (sConstruction 0 C) _⦋0⦌) → IsZeroVertex v` |
| `sConstructionZero_isContractibleKan` | `(C : SSet.{u}) → [Quasicategory C] → [HasZeroVertex C] → IsContractibleKan (sConstruction 0 C)` |
| `sConstructionZero_kanComplex` | 同じ C と前提に対し `KanComplex (sConstruction 0 C)` |
| `firstRowZero_hom_ext` | `(f g : A ⟶ (ihom (firstRowNerve 0)).obj C) → f = g` |
| `firstRowRestriction_zero_trivialKanFibration` | `(C : SSet.{u}) → [Quasicategory C] → [HasZeroVertex C] → TrivialKanFibration (firstRowRestriction 0 C)` |
| `arSquare_repeat_left` | `(i k l : Fin (n+1)) → (hik : i ≤ k) → (hkl : k ≤ l) → arSquare i i k l le_rfl hik hkl = CartesianMonoidalCategory.fst _ _ ≫ squareBottomEdge ≫ arSquare i i k l le_rfl hik hkl` |
| `arSquare_repeat_right` | `(i j k : Fin (n+1)) → (hij : i ≤ j) → (hjk : j ≤ k) → arSquare i j k k hij hjk le_rfl = CartesianMonoidalCategory.snd _ _ ≫ squareLeftEdge ≫ arSquare i j k k hij hjk le_rfl` |
| `arSquare_isPushout_of_repeated_endpoints` | `[Quasicategory C] → (F : arNerve n ⟶ C) → (i j k l : Fin (n+1)) → (hij : i ≤ j) → (hjk : j ≤ k) → (hkl : k ≤ l) → (i = j ∨ k = l) → IsPushoutSquare (arSquare i j k l hij hjk hkl ≫ F)` |
| `isGapped_one_of_zero_diagonal` | `[Quasicategory C] → (F : arNerve 1 ⟶ C) → (∀ j : Fin 2, IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj j j le_rfl)))) → IsGapped F` |
| `firstRowRestriction_trivialKanFibration_of_vertexSurjective` | `(n : ℕ) → (C : SSet.{u}) → [Quasicategory C] → [IsStable C] → Function.Surjective ((firstRowRestriction n C).app (Opposite.op ⦋0⦌)) → TrivialKanFibration (firstRowRestriction n C)` |
| `firstRowRestriction_one_vertex_surjective` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → Function.Surjective ((firstRowRestriction 1 C).app (Opposite.op ⦋0⦌))` |
| `firstRowRestriction_one_trivialKanFibration` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → TrivialKanFibration (firstRowRestriction 1 C)` |

零図式は実際の gapped 図式であり、始対象性と終対象性を関手圏から全部分複体へ移した。
S_0 の全頂点は零対象であるため、その境界を終対象性で充填して可縮 Kan 性を証明した。
次数0の第一行制限の結論は `HasZeroVertex C` だけで足りる。
次数1には、構成済みの零対角図式と、Fin 2 の四端点ではどちらかの組が等しいことを用いた。
一般次数の頂点全射性からの補題は条件付きであり、次数2以上の存在の代用にはしない。
S• の単体作用と零図式の両立は同型でなく頂点の厳密な等号である。

次数2の第一行制限を完成した。
Ar[2] の中央の四頂点 `(0,1),(0,2),(1,1),(1,2)` に一つの実際の cofiber 正方形を配置し、
外側の二つの対角を始対象・終対象による相対延長で補った。
構成は第一行と中央正方形を厳密に保つ。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `arTwoMiddleSquare` | `(Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ arNerve 2`、値は `arSquare 0 1 1 2 (by decide) le_rfl (by decide)` |
| `arTwoMiddleRetractionOrder` | `Ar.{u} 2 →o ULift.{u} (Fin 2 × Fin 2)` |
| `arTwoMiddleRetraction_order_comp` | `(arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor ⋙ arTwoMiddleRetractionOrder.toFunctor = 𝟭 _` |
| `arTwoMiddleRetraction` | `arNerve.{u} 2 ⟶ (Δ[1] ⊗ Δ[1] : SSet.{u})` |
| `arTwoMiddleSquare_retraction` | `arTwoMiddleSquare.{u} ≫ arTwoMiddleRetraction = 𝟙 _` |
| `arTwoMiddleSquare_mono` | `Mono arTwoMiddleSquare.{u}` |
| `arTwoMiddle` | `(arNerve.{u} 2).Subcomplex`、中央正方形の包含の像 |
| `arTwoMiddleIso` | `(Δ[1] ⊗ Δ[1] : SSet.{u}) ≅ (arTwoMiddle : SSet.{u})` |
| `arTwoMiddleIso_ι` | `arTwoMiddleIso.{u}.hom ≫ arTwoMiddle.ι = arTwoMiddleSquare` |
| `arTwo_obj_middle_or_endpoint` | `(a : Ar.{u} 2) → a = arObj 0 0 le_rfl ∨ a = arObj 2 2 le_rfl ∨ (a.down.val.1 ≤ 1 ∧ 1 ≤ a.down.val.2)` |
| `arTwoMiddleRetraction_obj_back` | `(a : Ar.{u} 2) → (a.down.val.1 ≤ 1) → (1 ≤ a.down.val.2) → (arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor.obj (arTwoMiddleRetractionOrder.toFunctor.obj a) = a` |
| `arTwoMiddleRetraction_square` | `arTwoMiddleRetraction.{u} ≫ arTwoMiddleSquare = nerveMap (arTwoMiddleRetractionOrder.toFunctor ⋙ (arSquareOrder (0 : Fin 3) 1 1 2 (by decide) le_rfl (by decide)).toFunctor)` |
| `arTwoMiddle_mem_of_vertices` | `(s : (arNerve.{u} 2) _⦋d⦌) → (∀ r, (s.obj r).down.val.1 ≤ 1 ∧ 1 ≤ (s.obj r).down.val.2) → s ∈ arTwoMiddle.obj (Opposite.op ⦋d⦌)` |
| `arTwoMiddle_vertices_of_mem` | `(s : (arNerve.{u} 2) _⦋d⦌) → s ∈ arTwoMiddle.obj (Opposite.op ⦋d⦌) → (r : Fin (d+1)) → (s.obj r).down.val.1 ≤ 1 ∧ 1 ≤ (s.obj r).down.val.2` |
| `arTwoMiddle_notMem_first` | `ComposableArrows.mk₀ (arObj (0 : Fin 3) 0 le_rfl) ∉ arTwoMiddle.{u}.obj (Opposite.op ⦋0⦌)` |
| `arTwoMiddle_notMem_last` | `ComposableArrows.mk₀ (arObj (2 : Fin 3) 2 le_rfl) ∉ arTwoMiddle.{u}.obj (Opposite.op ⦋0⦌)` |
| `arTwoMiddle_missing_endpoint` | `(s : (arNerve.{u} 2) _⦋d⦌) → s ∉ arTwoMiddle.obj (Opposite.op ⦋d⦌) → s.obj 0 = arObj 0 0 le_rfl ∨ s.obj (Fin.last d) = arObj 2 2 le_rfl` |
| `exists_arTwo_extension_with_zero_endpoints` | `(T : Square ⟶ C) → (z : C _⦋0⦌) → IsZeroVertex z → ∃ F : arNerve 2 ⟶ C, arTwoMiddleSquare ≫ F = T ∧ F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 0 0 le_rfl)) = z ∧ F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 2 2 le_rfl)) = z` |
| `isGapped_two_of_cofiber_middle` | `[Quasicategory C] → (F : arNerve 2 ⟶ C) → (T : ZeroTriangle C) → IsCofiberSequence T → arTwoMiddleSquare ≫ F = T.square → IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 0 0 le_rfl))) → IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj 2 2 le_rfl))) → IsGapped F` |
| `exists_gapped_arTwo_of_cofiber` | `[Quasicategory C] → (T : ZeroTriangle C) → IsCofiberSequence T → ∃ F : arNerve 2 ⟶ C, IsGapped F ∧ arTwoMiddleSquare ≫ F = T.square` |
| `firstRow_two_middle_bottom` | `(firstRowSimplexIso 1).hom ≫ firstRowInclusion.{u} 2 = squareBottomEdge ≫ arTwoMiddleSquare` |
| `exists_gapped_arTwo_with_firstRow` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → (p : firstRowNerve 2 ⟶ C) → ∃ F : arNerve 2 ⟶ C, IsGapped F ∧ firstRowInclusion 2 ≫ F = p` |
| `firstRowRestriction_two_vertex_surjective` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → Function.Surjective ((firstRowRestriction 2 C).app (Opposite.op ⦋0⦌))` |
| `firstRowRestriction_two_trivialKanFibration` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → TrivialKanFibration (firstRowRestriction 2 C)` |

中央の部分複体には新しいセルを付け足さず、残るセルの普遍的な端点で充填した。
次数2の唯一の非退化三つ組は `(0,1,2)` であり、中央の指定正方形そのものである。
他の三つ組には退化正方形の押し出し性を適用し、`isGapped_iff_triples` で全四つ組へ移した。
`exists_gapped_arTwo_of_cofiber` は実際の cofiber を入力すれば安定性を要求しない。
一般次数の存在はこの低次数の計算から自動的には従わない。

次数3以上の補完に向け、相対始対象からの射を基底の余錐上で選ぶ比較を証明した。
これは cofiber の零角・零射を固定する輸送のための準備であり、
固定した任意の零射の cofiber 存在そのものを完成扱いしない。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting` | `(a : (Δ[0] : SSet.{u}) ⟶ X) → (p : X ⟶ Y) → InitialBoundaryLifting p (SSet.yonedaEquiv a) → TrivialKanFibration (relativeCosliceMap a p (boundary 0))` |
| `sliceUnder_empty_hom_ext` | `(p : ((⊥ : K.Subcomplex) : SSet.{u}) ⟶ X) → (f g : A ⟶ sliceUnder p) → (f ≫ sliceUnderProjection p = g ≫ sliceUnderProjection p) → f = g` |
| `cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting` | `(a : (Δ[0] : SSet.{u}) ⟶ X) → (p : X ⟶ Y) → InitialBoundaryLifting p (SSet.yonedaEquiv a) → TrivialKanFibration (cosliceEndpointMap a p)` |
| `exists_relativeInitialCosliceLift` | `(a : (Δ[0] : SSet.{u}) ⟶ X) → (p : X ⟶ Y) → InitialBoundaryLifting p (SSet.yonedaEquiv a) → (i : A ⟶ B) → [Mono i] → (u : A ⟶ sliceUnder a) → (v : B ⟶ X) → (w : B ⟶ sliceUnder (a ≫ p)) → (v ≫ p = w ≫ sliceUnderProjection (a ≫ p)) → (u ≫ sliceUnderProjection a = i ≫ v) → (u ≫ sliceUnderPostcomp a p = i ≫ w) → ∃ F : B ⟶ sliceUnder a, i ≫ F = u ∧ F ≫ sliceUnderProjection a = v ∧ F ≫ sliceUnderPostcomp a p = w` |

上記の全宣言は X・Y・A・B の quasicategory 性、p の inner fibration 性、安定性を仮定しない。
比較写像の境界充填は、点と境界を貼った標準境界に `InitialBoundaryLifting` を適用して構成した。
端点比較は空図式上の coslice の射の一意性でこの比較へ移し、全単射の RLP から相対延長を得た。
Core と Stable のファイルには変更を加えていない。

相対始対象の可逆辺による輸送と、同型な図式の余極限の存在の輸送を証明した。
以下で `E,B,K,X : SSet.{u}`。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `stdSimplex_firstVertex_leftAnodyne` | `(n : ℕ) → leftAnodyneExtensions (SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin (n+1))) : (Δ[0] : SSet.{u}) ⟶ Δ[n])` |
| `pointCosliceVertexOfEdge_projection` | `(a : Δ[0] ⟶ E) → {y : E _⦋0⦌} → (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y) → (sliceUnderProjection a).app (Opposite.op ⦋0⦌) (pointCosliceVertexOfEdge a e) = y` |
| `InitialBoundaryLifting.of_invertibleEdge` | `[Quasicategory E] → [Quasicategory B] → (p : E ⟶ B) → [InnerFibration p] → (a : Δ[0] ⟶ E) → InitialBoundaryLifting p (SSet.yonedaEquiv a) → {y : E _⦋0⦌} → (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y) → IsInvertibleEdge e → InitialBoundaryLifting p y` |
| `InitialBoundaryLifting.of_vertexIso` | `[Quasicategory E] → [Quasicategory B] → (p : E ⟶ B) → [InnerFibration p] → {x y : E _⦋0⦌} → InitialBoundaryLifting p x → VertexIso x y → InitialBoundaryLifting p y` |
| `IsColimitCone.of_functorIso` | `[Quasicategory X] → {p q : K ⟶ X} → {c : JoinCocone p} → {d : JoinCocone q} → IsColimitCone c → FunctorIso c.val d.val → IsColimitCone d` |
| `isColimitCone_iff_of_functorIso` | `[Quasicategory X] → {p q : K ⟶ X} → (c : JoinCocone p) → (d : JoinCocone q) → FunctorIso c.val d.val → (IsColimitCone c ↔ IsColimitCone d)` |
| `IsPushoutSquare.of_functorIso` | `[Quasicategory X] → {F G : Square ⟶ X} → IsPushoutSquare F → FunctorIso F G → IsPushoutSquare G` |
| `exists_initialCoconeVertex_over_invertible_edge` | `(K X : SSet.{u}) → [Quasicategory X] → (v : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋0⦌) → InitialBoundaryLifting (coconeRestriction K X) v → (b : ((ihom K).obj X) _⦋0⦌) → (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) b ((coconeRestriction K X).app (Opposite.op ⦋0⦌) v)) → IsInvertibleEdge e → ∃ w, (coconeRestriction K X).app (Opposite.op ⦋0⦌) w = b ∧ InitialBoundaryLifting (coconeRestriction K X) w` |
| `HasColimit.of_functorIso` | `[Quasicategory X] → {p q : K ⟶ X} → HasColimit q → FunctorIso p q → HasColimit p` |
| `hasColimit_iff_of_functorIso` | `[Quasicategory X] → {p q : K ⟶ X} → FunctorIso p q → (HasColimit p ↔ HasColimit q)` |

相対始点境界充填の輸送では、基底の coslice の left fibration で最初の辺を全単体へ延ばし、
`exists_relativeInitialCosliceLift` で境界上の余錐を選び、可逆な最初の辺の相対外側ホーン充填を使った。
余極限の存在の輸送では、α-S の `exists_cartesian_cocone_lift` と F1 の
`isInvertibleEdge_of_isCartesianEdge` を読み取り専用で使用した。
新しい余錐は指定した図式に厳密に制限される。単なる頂点ごとの同型の族は使っていない。

次の接続：零角を持つ span のデータを、`zeroTargetArrowSource C` を第一辺の始点評価で
引き戻した対象として表す。同じ第一辺を持つ二つのデータはこの trivial Kan fibration の
可縮 fiber で同型となり、`stable_spanFamilyOfArrows` で全 span の関手同型に送れる。
上記の `HasColimit.of_functorIso` を選んだ cofiber の span に適用することで、指定した任意の零射を
保つ span の余極限の存在へ接続する。この接続は下記の `hasColimit_zeroSpan` で証明済み。

指定した零射を持つ span の余極限存在、および span 全体を固定した相対 cofiber 補完を証明した。
以下で `Span := (horn 2 0 : SSet.{u})`、`L := (pre horn₂₀.ι₀₁).app C`、
`R := (pre horn₂₀.ι₀₂).app C`、`s := evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))`、
`Zι := (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι`、
`ZeroSpanFamily d := ∀ v, IsZeroTargetArrow (R.app (Opposite.op ⦋0⦌) (d.app (Opposite.op ⦋0⦌) v))` と略記する。
この `ZeroSpanFamily` は表のための略記であり、追加の仮定や Lean 宣言ではない。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `zeroSpanData` | `(C : SSet.{u}) → SSet.{u}`、値は `pullback (zeroTargetArrowSource C) s` |
| `zeroSpanDataProjection` | `(C : SSet.{u}) → (zeroSpanData C ⟶ (ihom Δ[1]).obj C)`、値は引き戻しの第二射影 |
| `zeroSpanDataProjection_trivialKanFibration` | `(C : SSet.{u}) → [HasZeroVertex C] → TrivialKanFibration (zeroSpanDataProjection C)` |
| `zeroSpanDataDiagram` | `(C : SSet.{u}) → (zeroSpanData C ⟶ (ihom Span).obj C)` |
| `zeroSpanDataDiagram_left` | `zeroSpanDataDiagram C ≫ L = zeroSpanDataProjection C` |
| `zeroSpanDataDiagram_right` | `zeroSpanDataDiagram C ≫ R = pullback.fst (zeroTargetArrowSource C) s ≫ Zι` |
| `zeroSpan_sources` | `(C : SSet.{u}) → L ≫ s = R ≫ s` |
| `zeroSpanDataLift` | `(p : A ⟶ (ihom Span).obj C) → ZeroSpanFamily p → (A ⟶ zeroSpanData C)` |
| `zeroSpanDataLift_projection` | `(p : A ⟶ (ihom Span).obj C) → (hp : ZeroSpanFamily p) → zeroSpanDataLift p hp ≫ zeroSpanDataProjection C = p ≫ L` |
| `zeroSpanDataLift_diagram` | 同じ p・hp に対し `zeroSpanDataLift p hp ≫ zeroSpanDataDiagram C = p` |
| `zeroSpanFamiliesIso` | `[HasZeroVertex C] → (p q : A ⟶ (ihom Span).obj C) → ZeroSpanFamily p → ZeroSpanFamily q → (p ≫ L = q ≫ L) → FunctorIso p q` |
| `zeroSpanDiagramsIso` | `[HasZeroVertex C] → (p q : Span ⟶ C) → IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ p)) → IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ q)) → (horn₂₀.ι₀₁ ≫ p = horn₂₀.ι₀₁ ≫ q) → FunctorIso p q` |
| `hasColimit_zeroSpan` | `[Quasicategory C] → [IsStable C] → (p : Span ⟶ C) → IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ p)) → HasColimit p` |
| `cofiberSpan` | `(C : SSet.{u}) → (cofiberDiagrams C ⟶ (ihom Span).obj C)`、cofiber 四角形の二辺への制限 |
| `isZeroTargetArrow_pushoutSpan_iff` | `(F : Square ⟶ C) → (IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ pushoutSpan F)) ↔ IsZeroVertex (squareVertex F 0 1))` |
| `zeroSpanFamily_hasColimits` | `[Quasicategory C] → [IsStable C] → (d : B ⟶ (ihom Span).obj C) → ZeroSpanFamily d → (v : B _⦋0⦌) → HasColimit ((functorVertexEquiv Span C).symm (d.app (Opposite.op ⦋0⦌) v))` |
| `exists_relative_cofiberFamily_over_span` | `[Quasicategory C] → [IsStable C] → (i : A ⟶ B) → [Mono i] → (d : B ⟶ (ihom Span).obj C) → ZeroSpanFamily d → (a : A ⟶ cofiberDiagrams C) → (a ≫ cofiberSpan C = i ≫ d) → ∃ F : B ⟶ cofiberDiagrams C, i ≫ F = a ∧ F ≫ cofiberSpan C = d` |
| `cofiberSpan_pullback_trivialKanFibration` | `[Quasicategory C] → [IsStable C] → (d : B ⟶ (ihom Span).obj C) → ZeroSpanFamily d → TrivialKanFibration (pullback.snd (cofiberSpan C) d)` |
| `cofiberSpan_vertexFiber_isContractibleKan` | `[Quasicategory C] → [IsStable C] → (p : Span ⟶ C) → IsZeroTargetArrow (functorVertex (horn₂₀.ι₀₂ ≫ p)) → IsContractibleKan (vertexFiber (cofiberSpan C) (functorVertex p))` |
| `IsZeroSpanVertex` | `(v : ((ihom Span).obj C) _⦋0⦌) → Prop`、値は `IsZeroTargetArrow (R.app (Opposite.op ⦋0⦌) v)` |
| `zeroSpanDiagrams` | `(C : SSet.{u}) → SSet.{u}`、IsZeroSpanVertex による全部分複体 |
| `zeroSpanDiagrams_quasicategory` | `(C : SSet.{u}) → [Quasicategory C] → Quasicategory (zeroSpanDiagrams C)` |
| `cofiberSpanProjection` | `(C : SSet.{u}) → (cofiberDiagrams C ⟶ zeroSpanDiagrams C)` |
| `cofiberSpanProjection_ι` | `cofiberSpanProjection C ≫ (fullSubcomplexOnVertices _ IsZeroSpanVertex).ι = cofiberSpan C` |
| `cofiberSpanProjection_trivialKanFibration` | `(C : SSet.{u}) → [Quasicategory C] → [IsStable C] → TrivialKanFibration (cofiberSpanProjection C)` |

零脚の選択の比較には `zeroTargetArrowSource` の引き戻しの同じ fiber を使い、
`stable_spanFamilyOfArrows` で全 span の関手同型へ送った。選んだ cofiber の span の余極限を
`HasColimit.of_functorIso` で任意の指定零脚へ移している。
相対補完は、この実際の存在証明を `exists_relative_pushoutFamily` に入力し、
指定 span の零終点条件で cofiber 部分複体へ戻す。全ての等号は厳密で、追加の存在仮定を使わない。
これにより従来の第一辺だけを指定する `cofiberProjection` より強く、零角と零射も固定できる。

次の接続は、Ar[n] の各区間の span `(0,i)→(0,j),(i,i)` を枠から自然に取り出し、
`cofiberSpanProjection` の相対内部 Hom で枠と境界を同時に固定すること。
この全区間の図式と各三つ組の正方形の普遍性の接続は、まだ証明が必要である。

**未完了**：次数 n≥3 で零次元から作った実際の図式 F について、全三つ組の正方形
`arSquare i j j k hij le_rfl hjk ≫ F` が押し出しとなること。
零対角と第一行の厳密な回収、および三つ組から全四つ組への含意は証明済み。
cofiber 族の各区間の正方形が押し出しであることだけを、この F の三つ組の条件の代用にしない。
正次元の境界 RLP は全 n で証明済み、n=0・1・2 は全次元で証明済みだが、n≥3 の `boundary 0` が残るため、
`firstRowRestriction` の trivial Kan fibration と L1b 全体はまだ完了していない。
L1c–f は未着手。L1g は別途指示待ち。

零射を含む全 span の入力と、枠・既存境界を同時に固定する補完を接続した。
以下で `Span := (horn 2 0 : SSet.{u})`、`Square := Δ[1] ⊗ Δ[1]`、
`Zι := (fullSubcomplexOnVertices _ IsZeroSpanVertex).ι`、
`Fι := (fullSubcomplexOnVertices _ IsZeroFrameVertex).ι` と略記する。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `arCofiberZeroInputOrder` | `(n : ℕ) → (Ar.{u} n × ULift.{u} (Fin 2) →o FrameAr.{u} n)`、値は `(0,i)→(i,i)` |
| `arCofiberZeroInputMap` | `(n : ℕ) → (arNerve.{u} n ⊗ Δ[1] ⟶ frameNerve n)` |
| `arCofiberInputs_commonSource` | `(arNerve n ◁ stdSimplex.δ (1 : Fin 2)) ≫ arCofiberInputMap n = (arNerve n ◁ stdSimplex.δ (1 : Fin 2)) ≫ arCofiberZeroInputMap n` |
| `arCofiberSpan_isPushout` | `(n : ℕ) → IsPushout (arNerve.{u} n ◁ stdSimplex.δ (1 : Fin 2)) (arNerve n ◁ stdSimplex.δ (1 : Fin 2)) (arNerve n ◁ horn₂₀.ι₀₁) (arNerve n ◁ horn₂₀.ι₀₂)` |
| `arCofiberSpanMap` | `(n : ℕ) → (arNerve.{u} n ⊗ Span ⟶ frameNerve n)` |
| `arCofiberSpanMap_left` | `(arNerve n ◁ horn₂₀.ι₀₁) ≫ arCofiberSpanMap n = arCofiberInputMap n` |
| `arCofiberSpanMap_right` | `(arNerve n ◁ horn₂₀.ι₀₂) ≫ arCofiberSpanMap n = arCofiberZeroInputMap n` |
| `arCofiberSquareMap_left` | `(arNerve n ◁ squareLeftEdge) ≫ arCofiberSquareMap n = arCofiberZeroInputMap n ≫ frameInclusion n` |
| `arCofiberSquareMap_span` | `(arNerve n ◁ spanSquareBoundary) ≫ arCofiberSquareMap n = arCofiberSpanMap n ≫ frameInclusion n` |
| `frameCofiberSpanOperator` | `(n : ℕ) → (C : SSet.{u}) → ((ihom (frameNerve n)).obj C ⟶ (ihom (arNerve n)).obj ((ihom Span).obj C))` |
| `arCofiberFamilyOperator_span` | `arCofiberFamilyOperator n C ≫ (ihom (arNerve n)).map ((pre spanSquareBoundary).app C) = (pre (frameInclusion n)).app C ≫ frameCofiberSpanOperator n C` |
| `frameCofiberSquareMap_span` | `(frameNerve n ◁ spanSquareBoundary) ≫ frameCofiberSquareMap n = (frameInclusion n ▷ Span) ≫ arCofiberSpanMap n` |
| `frameCofiberFamilyOperator_span` | `frameCofiberFamilyOperator n C ≫ (ihom (frameNerve n)).map ((pre spanSquareBoundary).app C) = frameCofiberSpanOperator n C ≫ (pre (frameInclusion n)).app ((ihom Span).obj C)` |
| `frameCofiberSpanFamily` | `(F : frameNerve n ⟶ C) → (arNerve n ⟶ (ihom Span).obj C)` |
| `frameCofiberSpanOperator_vertex` | `(F : frameNerve n ⟶ C) → (frameCofiberSpanOperator n C).app (Opposite.op ⦋0⦌) (functorVertex F) = functorVertex (frameCofiberSpanFamily F)` |
| `frameCofiberSpanFamily_zero` | `(F : frameNerve n ⟶ C) → IsZeroFrameVertex (functorVertex F) → (a : Ar.{u} n) → IsZeroSpanVertex ((frameCofiberSpanFamily F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ a))` |
| `frameCofiberSpans` | `(n : ℕ) → (C : SSet.{u}) → (zeroFrameDiagrams n C ⟶ (ihom (arNerve n)).obj (zeroSpanDiagrams C))` |
| `frameCofiberSpans_ι` | `frameCofiberSpans n C ≫ (ihom (arNerve n)).map Zι = Fι ≫ frameCofiberSpanOperator n C` |
| `gappedCofiberFamiliesMap_span` | `gappedCofiberFamiliesMap n C ≫ (ihom (arNerve n)).map (cofiberSpanProjection C) = gappedFrameRestriction n C ≫ frameCofiberSpans n C` |
| `zeroFrameCofiberFamiliesMap_span` | `[Quasicategory C] → zeroFrameCofiberFamiliesMap n C ≫ (ihom (frameNerve n)).map (cofiberSpanProjection C) = frameCofiberSpans n C ≫ (pre (frameInclusion n)).app (zeroSpanDiagrams C)` |
| `exists_arCofiberSpanCompletion_preserving_frame` | `{A B C : SSet.{u}} → [Quasicategory C] → [IsStable C] → (n : ℕ) → (i : A ⟶ B) → [Mono i] → (a : A ⟶ sConstruction n C) → (b : B ⟶ zeroFrameDiagrams n C) → (a ≫ gappedFrameRestriction n C = i ≫ b) → ∃ H : B ⟶ (ihom (arNerve n)).obj (cofiberDiagrams C), i ≫ H = a ≫ gappedCofiberFamiliesMap n C ∧ H ≫ (ihom (arNerve n)).map (cofiberSpanProjection C) = b ≫ frameCofiberSpans n C ∧ H ≫ (pre (frameInclusion n)).app (cofiberDiagrams C) = b ≫ zeroFrameCofiberFamiliesMap n C` |

形状の段階で二辺を pushout により貼り、零対角条件で零脚つき span の内部 Hom へ持ち上げた。
相対補完は `cofiberSpanProjection` と `frameInclusion` の相対内部 Hom の trivial Kan fibration を使う。
したがって零頂点・零射を含む全 span と枠を、既存の境界に対して同時に厳密に固定できる。

**未完了の範囲は変わらない**：補完の右上角から得た実際の Ar[n] 図式の三つ組の正方形の普遍性
（n≥3 の零次元持ち上げ）が残る。cofiber 族自体の各正方形の普遍性を代用しない。
次は、この固定 span 条件から図式の標準単位との coherent な比較を作り、押し出しの貼り合わせで
三つ組の普遍性に接続する。L1b 全体と L1c–f は未完了、L1g は別途指示待ち。

この保存単位の検証：`lake build SerrePositivity.KST.SConstruction` 成功（2088 jobs）、
`lake env lean scripts/audit_kst_s_construction.lean` 成功（365 宣言、標準三公理のみ）。

標準 cofiber 正方形から図式自身の gapped 性への還元を証明した。
以下で `Span := (horn 2 0 : SSet.{u})`、`Square := Δ[1] ⊗ Δ[1]`、
`τ := (β_ (Δ[1] : SSet.{u}) Δ[1]).hom` と略記する。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `spanTranspose` | `Span ⟶ Span` |
| `spanTranspose_left` | `horn₂₀.ι₀₁ ≫ spanTranspose = horn₂₀.ι₀₂` |
| `spanTranspose_right` | `horn₂₀.ι₀₂ ≫ spanTranspose = horn₂₀.ι₀₁` |
| `spanTranspose_comp_self` | `spanTranspose ≫ spanTranspose = 𝟙 Span` |
| `spanTransposeIso` | `Span ≅ Span` |
| `spanTranspose_isIso` | `IsIso spanTranspose` |
| `spanTranspose_square` | `joinMap spanTranspose (𝟙 (Δ[0] : SSet.{u})) ≫ spanCoconeSquareIso.hom = spanCoconeSquareIso.hom ≫ τ` |
| `IsPushoutSquare.transpose` | `{C : SSet.{u}} → [Quasicategory C] → {F : Square ⟶ C} → IsPushoutSquare F → IsPushoutSquare (τ ≫ F)`、宣言は本レーンの namespace 内 |
| `arVerticalRectangleOrder` | `{n : ℕ} → (i j k l : Fin (n + 1)) → (hij : i ≤ j) → (hjk : j ≤ k) → (hkl : k ≤ l) → (ULift.{u} (Fin 3 × Fin 2) →o Ar.{u} n)` |
| `arVerticalRectangle` | 同じ i,j,k,l,hij,hjk,hkl に対し `(Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ arNerve n` |
| `arVerticalRectangle_left` | 同じ引数で `pastingSquare (arVerticalRectangle i j k l hij hjk hkl) 2 = τ ≫ arSquare i j k l hij hjk hkl` |
| `arVerticalRectangle_outer` | 同じ引数で `pastingSquare (arVerticalRectangle i j k l hij hjk hkl) 1 = τ ≫ arSquare i k k l (hij.trans hjk) le_rfl hkl` |
| `arVerticalRectangle_right` | 同じ引数で `pastingSquare (arVerticalRectangle i j k l hij hjk hkl) 0 = τ ≫ arSquare j k k l hjk le_rfl hkl` |
| `arTriple_isPushout_of_originSquares` | `{n : ℕ} → {C : SSet.{u}} → [Quasicategory C] → (F : arNerve n ⟶ C) → (∀ (i j : Fin (n + 1)) (hij : i ≤ j), IsPushoutSquare (arSquare 0 i i j (Fin.zero_le _) le_rfl hij ≫ F)) → (i j k : Fin (n + 1)) → (hij : i ≤ j) → (hjk : j ≤ k) → IsPushoutSquare (arSquare i j j k hij le_rfl hjk ≫ F)` |
| `isGapped_iff_originSquares` | `{n : ℕ} → {C : SSet.{u}} → [Quasicategory C] → (F : arNerve n ⟶ C) → (IsGapped F ↔ (∀ i : Fin (n + 1), IsZeroVertex (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (arObj i i le_rfl)))) ∧ (∀ (i j : Fin (n + 1)) (hij : i ≤ j), IsPushoutSquare (arSquare 0 i i j (Fin.zero_le _) le_rfl hij ≫ F)))` |
| `isGapped_iff_arCofiberFamily_vertices` | `{n : ℕ} → {C : SSet.{u}} → [Quasicategory C] → (F : arNerve n ⟶ C) → (IsGapped F ↔ ∀ a : (arNerve n) _⦋0⦌, IsCofiberDiagramVertex ((arCofiberFamily F).app (Opposite.op ⦋0⦌) a))` |

転置は span の二終点の交換を同型として構成し、その同型による余錐の制限で証明した。
還元は、標準正方形 `(0,i,i,j)` と `(0,i,i,k)` の横方向の相殺で `(0,i,j,k)` を得た後、
これと `(0,j,j,k)` の縦方向の相殺で `(i,j,j,k)` を得る。既存の三つ組判定で全四つ組へ進む。
退化した端点も全て含み、安定性・余極限の存在・零対角条件は押し出し部分の還元に要求しない。

**現在地・未完了**：L1a は完了。L1b は全次数の正次元境界 RLP と n=0,1,2 の全境界 RLP が証明済み。
任意の単射上で枠・span・既存境界を厳密に保つ cofiber 補完も証明済み。
n≥3 の零次元持ち上げでは、得られた図式 F の標準抽出 `arCofiberFamily F` が選んだ cofiber 族と
coherent に比較できることが残る。上記の同値により、その比較から gapped 性への含意は証明済み。
選んだ cofiber 族の各正方形の普遍性を図式自身の正方形の普遍性と取り違えない。
次は枠での厳密な一致と固定 span 条件からこの比較を構成する。
L1c–f は未完了、L1g は別途指示待ち。

この保存単位の検証：`lake build SerrePositivity.KST.SConstruction` 成功（2090 jobs）、
`lake env lean scripts/audit_kst_s_construction.lean` 成功（381 宣言、標準三公理のみ）。

枠の指定だけから、単位の中間正方形と補完後の図式の標準正方形との関手同型を証明した。
以下で `Square := (Δ[1] ⊗ Δ[1] : SSet.{u})`、`top := (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2)) : Square _⦋0⦌`、
`q a := arSquare 0 a.down.val.1 a.down.val.1 a.down.val.2 (Fin.zero_le _) le_rfl a.down.property`、
`J a := arCofiberUnitPrism a`、`D a := arCofiberUnitSquare a`、
`e := lift (𝟙 (arNerve n)) (SSet.const top)`、`ι := (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι` と略記する。
また `row k := ComposableArrows.mk₀ (⟨arObj 0 k (Fin.zero_le _), Or.inl rfl⟩ : FrameAr.{u} n)`、
`v x y := (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) : Square _⦋0⦌` とする。
これらの q・J・D・e・row・v はこの表のための略記であり、追加の仮定ではない。

| 公開宣言 | 正確な型・前提 |
| --- | --- |
| `intervalMaxOrder` | `ULift.{u} (Fin 2 × Fin 2) →o ULift.{u} (Fin 2)`、値は max |
| `intervalMax` | `Square ⟶ (Δ[1] : SSet.{u})` |
| `intervalMax_zero` | `prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ intervalMax = 𝟙 Δ[1]` |
| `intervalMax_one` | `prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ intervalMax = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))` |
| `cofiberUnitCornerPrism` | `(Δ[1] : SSet.{u}) ⊗ Square ⟶ Square`、値は `(t,(x,y)) ↦ (1,max t y)` |
| `arCofiberUnitPrism` | `{n : ℕ} → (a : Ar.{u} n) → ((Δ[1] : SSet.{u}) ⊗ Square ⟶ arNerve n ⊗ Square)`、値は `(t,s) ↦ (q a(s),(1,max t s.2))` |
| `cofiberUnitCorner` | `Square ⟶ Square`、値は `(x,y) ↦ (1,y)` |
| `cofiberUnitCornerPrism_zero` | `prismEndpoint 0 Square ≫ cofiberUnitCornerPrism = cofiberUnitCorner` |
| `cofiberUnitCornerPrism_one` | `prismEndpoint 1 Square ≫ cofiberUnitCornerPrism = SSet.const top` |
| `arCofiberUnitSquare` | `{n : ℕ} → (a : Ar.{u} n) → (Square ⟶ arNerve n ⊗ Square)`、値は `lift (q a) cofiberUnitCorner` |
| `arCofiberUnitPrism_zero` | `(a : Ar.{u} n) → prismEndpoint 0 Square ≫ J a = D a` |
| `arCofiberUnitPrism_one` | `(a : Ar.{u} n) → prismEndpoint 1 Square ≫ J a = q a ≫ e` |
| `arCofiberUnitPrism_lower` | `(a : Ar.{u} n) → (x : Fin 2) → lift (𝟙 Δ[1]) (SSet.const (v x 0)) ≫ J a = lift (SSet.const (row (intervalStep a.down.val.1 a.down.val.2 a.down.property x))) squareRightEdge ≫ (frameInclusion n ▷ Square)` |
| `arCofiberUnitPrism_upper` | `(a : Ar.{u} n) → (x : Fin 2) → lift (𝟙 Δ[1]) (SSet.const (v x 1)) ≫ J a = SSet.const (ComposableArrows.mk₀ (arObj a.down.val.1 (intervalStep a.down.val.1 a.down.val.2 a.down.property x) (le_intervalStep _ _ _ _)), top)` |
| `frameCofiberSquareMap_row_right` | `(k : Fin (n + 1)) → lift (SSet.const (row k)) squareRightEdge ≫ frameCofiberSquareMap n = SSet.const (row k)` |
| `arCofiberUnitPrism_vertex_constant` | `(E : arNerve n ⊗ Square ⟶ C) → (F : frameNerve n ⟶ C) → ((frameInclusion n ▷ Square) ≫ E = frameCofiberSquareMap n ≫ F) → (a : Ar.{u} n) → (v : Square _⦋0⦌) → ∃ z : C _⦋0⦌, lift (𝟙 Δ[1]) (SSet.const v) ≫ (J a ≫ E) = SSet.const z` |
| `arCofiberUnitComparisonIso` | `[Quasicategory C] → (E : arNerve n ⊗ Square ⟶ C) → (F : frameNerve n ⟶ C) → ((frameInclusion n ▷ Square) ≫ E = frameCofiberSquareMap n ≫ F) → (a : Ar.{u} n) → FunctorIso (D a ≫ E) (q a ≫ e ≫ E)` |
| `arSquareFamilyDiagram` | `(H : arNerve n ⟶ (ihom Square).obj C) → (arNerve n ⊗ Square ⟶ C)`、値は `(β_ (arNerve n) Square).hom ≫ uncurry H` |
| `arSquareFamilyDiagram_evaluate` | `(H : arNerve n ⟶ (ihom Square).obj C) → (v : Square _⦋0⦌) → lift (𝟙 (arNerve n)) (SSet.const v) ≫ arSquareFamilyDiagram H = H ≫ evaluateFunctorAt v` |
| `arSquareFamilyDiagram_frame` | `(H : arNerve n ⟶ (ihom Square).obj C) → (F : frameNerve n ⟶ C) → (frameInclusion n ≫ H = frameCofiberFamily F) → (frameInclusion n ▷ Square) ≫ arSquareFamilyDiagram H = frameCofiberSquareMap n ≫ F` |
| `arSquareFamilyUnitComparisonIso` | `[Quasicategory C] → (H : arNerve n ⟶ (ihom Square).obj C) → (F : frameNerve n ⟶ C) → (frameInclusion n ≫ H = frameCofiberFamily F) → (a : Ar.{u} n) → FunctorIso (D a ≫ arSquareFamilyDiagram H) (q a ≫ H ≫ evaluateFunctorAt top)` |
| `cofiberFamilyUnitComparisonIso` | `[Quasicategory C] → (H : arNerve n ⟶ cofiberDiagrams C) → (F : frameNerve n ⟶ C) → (hF : IsZeroFrameVertex (functorVertex F)) → (frameInclusion n ≫ H = zeroFrameCofiberFamily F hF) → (a : Ar.{u} n) → FunctorIso (D a ≫ arSquareFamilyDiagram (H ≫ ι)) (q a ≫ H ≫ cofiberApex C)` |

全ての型で省略した n・C は `{n : ℕ} {C : SSet.{u}}`。比較の下側の角では枠内の第一行の右辺が恒等、
上側の角では prism 自体が定値なので、全ての縦辺が恒等辺となる。
`functorIsoOfEquivalenceHomotopy` を用いて、点ごとの恒等性を関手単体集合の実際の同型へ送った。
この比較は cofiber 族の各正方形の押し出し性や C の安定性を使わない。

**現在地・未完了**：この同型は「単位の中間正方形 → 図式の標準抽出」の比較である。
中間正方形 `D a ≫ arSquareFamilyDiagram (H ≫ ι)` 自体が押し出しであることはまだ証明していない。
次は固定 span の等号と H(a) の cofiber 普遍性からこの中間正方形の普遍性を導く。
前の `isGapped_iff_originSquares` により、これを全 a で示せば補完後の実際の図式の gapped 性へ進める。
L1b の n≥3 の零次元持ち上げは引き続き未完了。L1a 完了、L1c–f 未完了、L1g は別途指示待ち。

この保存単位の検証：`lake build SerrePositivity.KST.SConstruction` 成功（2092 jobs）、
`lake env lean scripts/audit_kst_s_construction.lean` 成功（403 宣言、標準三公理のみ）。
