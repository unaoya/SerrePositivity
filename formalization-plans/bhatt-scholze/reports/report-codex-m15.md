# BS-M15（⑤d）作業報告

## 現在地（2026-11-17）

- レーン：⑤d（M15・G12、枝 `math/bs-m15`）。指示書：[bhatt-scholze-codex-m15.md](../instructions/bhatt-scholze-codex-m15.md)。
- 今の段：G12（CAlg の presentability）の G01。次のまとまり（部分豊穣圏・filtration・全付着の普遍性）の見込み 3,000〜5,200 行が残枠 1,041 行に収まらず、Lean の追加を停止（§129）。BS-M15 §9・D81 の受領後は紙のみ（§130〜§132）。
- 一覧：G12 済み 0／全体 15（うち追加 0）。M15 済み 10／全体 43（うち追加 1）（§129・§132）。
- 最新の検証済みコミット：8bd16ab2b（§128。179 ファイル・18,959 行・899 明示監査根）。§129 の報告は 37fe25328。main は b8c8f47a5 を確認（§130）。
- 外枠と行数：G12 の外枠 20,000 行、検証済み 18,959 行、残枠 1,041 行。M15 の 16,936 行はこの集計に含めない（§129）。
- 残り：G01 の残りと G02〜G15（一般／BE に分けた型つき残量は §131）。M15 は 5∞-2 待ち（§129〜§132）。
- 停止の内容：Lean は 8bd16ab2b で凍結。D81 により BS の CAlg は HA の方向で作り、旧 G01〜G15 の BE 適用の扱いは未決（§130）。5a-4・S7 の入力を G12 全体を通らずに得る候補は §132。
- 待ち：ユーザーの判断（外枠・進める範囲、D81 後の BE の扱い）（§129・§130）。

## 終わった段（archive）

- [§1〜§5　M15 段 0 と D80 後の加群関手](../../archive/reports/report-codex-m15-stage0.md)
- [§6〜§13　M10 着手前の接続と B4](../../archive/reports/report-codex-m15-m10-b4.md)
- [§14〜§25　M15 再開・M10 着手・N01](../../archive/reports/report-codex-m15-m10-n01.md)
- [§26〜§42　M10 の Hom 比較（約 8,500 行の途中報告まで）](../../archive/reports/report-codex-m15-m10-hom.md)
- [§43〜§70　M10 の cone、外枠の停止、停止時の紙](../../archive/reports/report-codex-m15-m10-cone.md)
- [§71〜§74　G12 段 0](../../archive/reports/report-codex-m15-g12-stage0.md)
- [§75〜§102　G01 前半（約 10,000 行の途中報告まで）](../../archive/reports/report-codex-m15-g01-1.md)
- [§103〜§128　G01 後半（実親子の全単射まで）](../../archive/reports/report-codex-m15-g01-2.md)

## §129 G12：次の全付着のまとまりと残枠の再評価、Lean追加の停止（11-16）

### 129.1 今回確認した境界

main の BS-M15 §8 を読み直した。承認された外枠は20,000行であり、
G01〜G15の完成・G09の途中取り込みとは別の制約である。
§128のコミット8bd16ab2bの後、作業木は清潔で、
InfinityCategories/HA/Monads/ の実ファイルを再集計すると179ファイル・18,959行。
残枠は **1,041行**。M15の16,936行と報告・監査資料はこの集計に加えない。

現在あるのはWalkingAdjunctionEnrichment.leanの実豊穣圏、全次数の原子的な道の
自由性の部品、幅・面・退化・実親の計算と、§128の実親子の全単射である。
WalkingAdjunctionAtomicCell.NativeFillableは現在の有限順序模型の条件であり、
これだけで原典の全付着や、元の随伴からのcoherentな延長が完成したとはしない。
NativeMonad.leanには全作用の構造とそのendofunctorがあるが、
元のQCatAdjunctionからその作用を作るinducedNativeMonadはまだない。

次のまとまりは、親子の対応を使った **部分豊穣圏・filtration・全付着の普遍性**。
さらに細かい法則を足して残枠を使い切る前に、このまとまりの費用を再評価した。
MathlibのEnriched/EnrichedCat.leanでは束ねた豊穣圏・豊穣関手・双圏の部品を確認したが、
今回の二種類の付着の普遍性は同ファイルからそのまま取り出せなかった。
これはMathlib全体に一般構成がないという結論ではなく、調査した入口の結果である。
SSet.Subcomplex・toSSet・ι・homOfLEは再利用可能であり、作り直す予定にしない。

### 129.2 次のまとまりの検収型（紙、未実装）

以下はG01内部の検収仕様であり、新しい一覧ID・既存Lean宣言・検証済みコードではない。
Aを現在のwalking adjunctionの部分豊穣圏とし、そのHomを
S X Y : (WalkingAdjunctionHomShape X Y).Subcomplexで表示する。
各Sは指定単位を含み、walkingAdjunctionCompositionの下で閉じる。
同じ部分型のHomに実際の豊穣圏構造を入れ、包含は元の全単体写像で与える。
生成閉包は面・退化・水平合成の下で閉じた最小のものとし、
非fillableな原子を含むときはその実親を含むというparental条件も検収する。

検収する出力の型は次のとおり（添字・全関手名は仕様上の略記）。

```text
S_i : (X Y : WalkingAdjunctionPoint) →
  (WalkingAdjunctionHomShape X Y).Subcomplex       (i : ℕ)
S_0 = S_A
∀ i X Y, S_i X Y ≤ S_(i+1) X Y
∀ X Y, (⨆ i, S_i X Y) = S_A' X Y

X_i : Finset (Σ n Y, {p : WalkingAdjunctionAtomicCell (n+1) .minus Y //
                       p.NativeFillable})
-- 実際に追加する親の有限族。空の段を許す表示ならその扱いも固定する。
-- 各親は前段に含まれず、指定面を除く全ての面が前段に含まれる。
-- 次段は前段とX_iの生成閉包そのもの。

-- 各段で、前段の包含は以下の二種類の付着の和のpushout：
2[Λ[n,k]] → 2[Δ[n]]       (0 < k < n)
3[∂Δ[n-1]] → 3[Δ[n-1]]   (k = n)
```

pushoutは単なるHomの包含・集合の和の等式ではなく、任意の標的豊穣圏Kと
前段からの豊穣関手Fについて、次段への延長の型が、対応する境界上でFと一致する
付着セルの像の型と同値になる普遍性として証明する。
制限と延長は実豊穣関手で、両方向の往復、単体作用・合成との両立を含む。
その後のcoherent延長では、前者に準圏のinner horn充填を、
後者に同じ余単位のslice内の終対象の普遍性を適用する必要が残る。

原典の該当箇所は[Riehl–Verity](https://emilyriehl.github.io/files/adjunctions.pdf)
Definition 4.2.9、Lemma 4.2.10、Corollary 4.2.13、Proposition 4.2.15、§4.3。
水平反対の現在の模型への移送と原典の条件との照合も、証明対象に含める。
原典の定理を未証明のinstanceや延長データの仮定として加える計画ではない。

### 129.3 補正つきの追加見込みと停止判断

| 次のまとまりの内訳（G01内部） | 素の追加見込み | 補正後（係数2） |
|---|---:|---:|
| 部分豊穣圏・生成閉包・parental条件、模型の条件と付着の条件の照合 | 450–750 | 900–1,500 |
| 実幅・深さ・次数によるfiltration、全ての非指定面の前段所属・全体の回収 | 400–700 | 800–1,400 |
| 二種類のセルと実延長、有限同時付着の普遍性・往復 | 650–1,150 | 1,300–2,300 |
| **次のまとまりのみの追加量** | **1,500–2,600** | **3,000–5,200** |

この数字は計画上の留保であり、形式的な下界や保証された上界ではない。
既存の幅の不等式・自由な道・親子の全単射は再加算しない。
一方、集合上の生成から実豊穣関手の延長へ移る部分は未経験なので係数1にしない。
§127–§128では、実原子・親子を一体化し両方向の往復までまとめるだけで621行を要した。
上表の未着手の三つの検収を残枠1,041行へ収める計画は採用できない。
また、旧§74のG01〜G03全体の上端3,200行に対して現在18,959行（約5.92倍）でも
G01が未完である。この比は未完の束との比較であり、個別作業の確定倍率ではないが、
旧見込みを今後の残量にもそのまま適用できない根拠である。

次のまとまりまでを加えた計画値だけで総量21,959–24,159行となる。
**これはG01全体やG12完成の見込みではない**。
元のQCatAdjunctionからの全coherent延長、同じF≫U・単位・余単位、
水平反対の向き・HAとの比較、およびG02〜G15はこの表の後にも残る。
従って24,159行を新しい完成外枠として提案したことにはしない。

BS-M15 §8の20,000行の外枠を維持するため、ここで **G12のLean追加を止める**。
G12完成・G09完成としては報告せず、検証済みを保持して、外枠・進める範囲の指示を求める。
これは10,000行の途中報告で止まる判断ではなく、次の未完のまとまりが外枠に収まらないという再評価である。

### 129.4 今回の変更と進み

変更は本報告の追記のみ。Lean追加・既存Leanの変更・ビルド・公理監査は行っていない。
検証済みは§128の179ファイル・18,959行・899明示監査根のまま。
今回の紙上の型・費用見込みを検証済みLeanとして数えない。
main・drafts・他レーン・⑤aの既存ファイル・Interface・M15は変更していない。
ゴールは未達。M15の5∞-2待ちは維持する。

G12：**一覧：済み 0／全体 15（うち追加 0）**。G01未完、検証済み18,959／20,000行。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。


## §130 BS-M15 §9・D81の受領と、今回の紙の前提（11-16）

ユーザー判断とmain b8c8f47a5のBS-M15 §9を確認した。
G12の外枠20,000行を変えず、Leanは8bd16ab2bの179ファイル・18,959行で凍結する。
37fe25328の§129も保持する。今回は報告だけを追記し、mainの取り込み、Leanの追加・変更、
ビルド、鍵取得、公理監査はしない。M15は5∞-2待ちのまま。

D81により、BSが採用するCAlgはHAの方向で作る。
BEを計算用模型として残して整流で結ぶか、使わないか、Interface・D79・D80の扱いは未決である。
従って、旧G01〜G15のBE適用を今後も必須とはしないが、決定前に費用を0として削除もしない。
以下は凍結解除や新しい実装の承認を求める一覧ではなく、残量と経路を比較する紙である。

確認した利用側は、mainのstage-ii/inf-supply-w1.md、
report-bs-infinity-a1-stage0.mdのS7先行判定・型つき一覧、
stage-ii-second-half.mdの5a-4m・S7の追記、drafts/Sheaves/CAlgValued.lean。
古いinfinity-sheaves-design.mdのS7はD(A)への適用を指すが、今回のS7は
現在の一覧にあるCAlg値の層化・忘却・RΓの比較を指す。
calg-interface-design.mdのD75に基づく経路の記述は歴史的記録として読み、D81で上書きする。

原典は次を本文で照合した（以下HA・HTT・RVと略す）。

- [HA、2017-09-18版](https://www.math.ias.edu/~lurie/papers/HA.pdf)：
  1.3.5.21、2.2.1.6–2.2.1.9、3.2.2.4–3.2.2.6、3.2.3.1–3.2.3.5、
  4.2.3.3–4.2.3.7、4.7.2–4.7.3（特に4.7.3.3–4.7.3.5）。
- [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf)：
  5.4.7.3・5.4.7.11、5.5.1.1、5.5.4.15、5.5.8.17、6.2.2.7とその証明の構成。
- [RV, Homotopy coherent adjunctions and the formal theory of monads](https://emilyriehl.github.io/files/adjunctions.pdf)：
  4.2.10・4.2.15・4.3.9、5.2.4、6.1.7–6.1.9・6.1.14、6.3.7–6.3.8・6.3.15–6.3.17、
  7.1.9・7.2.1・7.2.4・7.2.7。
- Kerodon [6.2.1.4、Tag 02EN](https://kerodon.net/tag/02EN)、
  [9.7.2、Tag 02QD](https://kerodon.net/tag/02QD)、
  [9.7.2.1、Tag 02QE](https://kerodon.net/tag/02QE)、
  [9.7.2.9、Tag 02QN](https://kerodon.net/tag/02QN)、
  [9.7.2.10、Tag 02QP](https://kerodon.net/tag/02QP)。
  02ENはホモトピー双圏での随伴の照合であり、全coherentモナド構成の代用ではない。

## §131 G01の残り・G02〜G15：一般理論と旧BE適用を分けた型つき残量（紙）

### 131.1 記法・数え方

C,BはSSet.{u+1}の準圏、F : C ⟶ B、U : B ⟶ C、a : QCatAdjunction F U。
Tは全coherentなNativeMonad C、EM(T)はこれから構成する実代数準圏、
F_T・U_Tはその自由・忘却、q_aは指定比較とする。
BEではC=D(A)、B=CAlg_R A、a_BE=cAlgFreeForgetDerivedAdjunction A、
U_BE=cAlgForgetDerived A、T_BE=inducedNativeMonad a_BE。
一般の図式は小さいKをuliftしたnative図式。simpはulift N(Δᵒᵖ)。
P(C,E)はsite C上のE値前層準圏。以下の未構成名・略記は**紙の仕様**であり、
Leanで宣言した型・コンパイル済みの結果としては扱わない。

各IDの一般部分と適用部分は同じ主出力の分担であり、一覧の項目を増やさない。
全作用・実関手・全関手同型・元の錐を検収し、h圏だけの主張に弱めない。
係数2は各区間の両端へ掛ける。素の値も空行・import・docstring・法則・証明分割を含む。
これは将来必要となるLean行数の計画値であり、紙の行数ではない。

### 131.2 型つきの一覧（一般／BEの両方を明記）

| ID | 一般の∞モナドの理論：残る出力の型・原典 | BEの模型CAlg_Rへの適用：残る出力の型 |
|---|---|---|
| G01 | `inducedNativeMonad a : NativeMonad C`、`FunctorIso (inducedNativeMonad a).endofunctor (F ≫ U)`。同じ単位・余単位から全作用を構成。HA 4.7.3.2–3、RV 4.2.10・4.2.15・4.3.9、Kerodon 6.2.1.4 (02EN)への忘却比較 | `T_BE : NativeMonad (D(A))` と `FunctorIso T_BE.endofunctor (cAlgFreeDerived A ≫ U_BE)`。既存の実随伴へ代入し、同じ成分との比較を検収 |
| G02 | `EM(T) : SSet.{u+1}`、`Quasicategory (EM(T))`、`U_T : EM(T) ⟶ C`。HA 4.7.2、RV 5.2.4・6.1.7–9 | `EM(T_BE)`と`U_T_BE`は一般出力の特殊化。BE固有の新しい構成はなし。`B ≃ EM(T_BE)`はここで数えずG09 |
| G03 | `F_T : C ⟶ EM(T)`、`QCatAdjunction F_T U_T`、`FunctorIso (F_T ≫ U_T) T.endofunctor`。HA 4.7.2、RV 6.1.14 | G07の`q_BE`に対し`FunctorIso (cAlgFreeDerived A ≫ q_BE) F_T_BE`。元の自由関手・単位の照合 |
| G04 | `nativeBar a : B ⟶ NativeAugmentedBar B`。全次数の値は`(F U)^(n+1)`、増大は元の余単位。HA 4.7.2、RV 6.3.15–17・7.1.9 | 元の`strictBarAugmentedFunctor`の局所化後の全図式と`nativeBar a_BE`の`FunctorIso`。頂点・次数別の同型だけにしない |
| G05 | `∀ X, IsUSplit U (nativeBar a X).underlying`、全増大と追加退化の比較。HA 4.7.2、RV 6.3.15–17・7.2.1 | BEの既存の厳密barの単位・余単位・全分裂との同じ図式上の比較 |
| G06 | EM側で`∀ D : simp ⟶ EM(T), IsUSplit U_T D → ∃ c, IsColimitCone c ∧ IsColimitCone (mapJoinCocone U_T c)`。一般のUには同じ式を条件として定義し、無条件の定理にはしない。HA 4.7.2、RV 6.3.7–8 | **元のG06の本体**：`∀ D : simp ⟶ B, IsUSplit U_BE D → ∃ c, IsColimitCone c ∧ IsColimitCone (mapJoinCocone U_BE c)`。任意のnative入力。実現側の未供給の橋を含む |
| G07 | `q_a : B ⟶ EM(inducedNativeMonad a)`、`FunctorIso (q_a ≫ U_T) U`。HA 4.7.3.4、RV 7.1.9 | 同じ`q_BE`と元の`U_BE`との全比較。台の随伴が別の模型へ変わっていないことを照合 |
| G08 | `IsConservative U → USplitRealizationCondition U → IsFullyFaithful q_a`。HA 4.7.3.5、RV 7.2.4・7.2.7の比較の証明 | 既存のBE忘却の保守性とG06を代入し、`IsFullyFaithful q_BE`。全写像空間を検収 |
| G09 | 同じ条件から`IsEssentiallySurjective q_a`、`IsQCatEquivalence q_a`。HA 4.7.3.5、RV 7.2.7 | `q_BE`の同じU上の同値と指定逆・比較を得る。BE適用を残すなら旧途中取り込み点 |
| G10 | accessibleなU・Tに対し、共通のregular κとnativeなκ-filtered保存を選ぶ。`∃ κ, Regular κ ∧ IsKappaAccessibleFunctor κ U ∧ IsKappaAccessibleFunctor κ T.endofunctor`。HA 4.7.3の作用、HTT 5.4.7の濃度の部品 | 普通のdg代数のfiltered保存から`U_BE`のnative保存を実際に照合し、同じκで`T_BE.endofunctor`も扱う。ordinary IsCardinalAccessibleの単なる読み替えにはしない |
| G11 | `IsPresentable C → IsAccessibleFunctor T.endofunctor → IsAccessible (EM(T))`。HA 4.2.3.4をAccに適用する経路、HTT 5.4.7.3・5.4.7.11、RV 6.1.7の模型との比較 | 一般定理への代入のみ。CAlg_Rへの移送はG13に計上 |
| G12 | `IsPresentable C → IsAccessibleFunctor T.endofunctor → HasSmallColimits (EM(T))`。全小図式の実余錐を構成。HA 4.7.2の自由解像度・4.2.3.5の保存される形の創出、HTT 5.5.1.1。RV 6.3.8はTが保つ形の部品 | 一般定理への代入のみ。CAlg_Rへの移送はG14に計上 |
| G13 | `IsAccessible C → QCatEquivalence C B → IsAccessible B`。HTT 5.4.2の定義・5.5.1.1に沿う不変性。既存`isAccessible_iff_equivalence`を再利用 | `IsAccessible (CAlg_R A)`をG09・G11から、同じ宇宙・元のBへ移す |
| G14 | `HasSmallColimits C → QCatEquivalence C B → HasSmallColimits B`。既存`HasSmallColimits.of_equivalence`を再利用（HTT 5.5.1.1の余極限条件） | `HasSmallColimits (CAlg_R A)`と全指定余錐をG09・G12から戻す |
| G15 | `IsAccessible B → HasSmallColimits B → IsPresentable B`。既存の定義・`IsPresentable.of_equivalence`（HTT 5.5.1.1） | `@IsPresentable (barrattEcclesCore.CAlg A) (barrattEcclesCore.quasicategory A)`、旧Interfaceの欄との同じ型の検収。D81でこの実例を残すかは未決 |

G10の一般部分の前提にはUのaccessibilityを含む。任意の右随伴について無条件に
accessibilityを作る主張ではない。BEに対してその前提を証明する費用は右欄にある。
G11–G12ではaccessibleなTを「全余極限を保つT」に強めない。
HA 4.2.3.7の各作用が全余極限を保つという仮定を、そのままEnd(C)全体へ置くこともできない。
G12の記載番号は証明に使う部品であり、4.2.3.5だけで全余極限の存在が出るという引用ではない。
必要なaccessibleな代数の表示・自由解像度と小図式の構成の費用を下に残した。

### 131.3 項目ごとの残量（追加Lean行数、素の値／係数2）

| ID | 一般：素 | 一般：×2 | BE適用：素 | BE適用：×2 |
|---|---:|---:|---:|---:|
| G01の残り | 4,000–7,500 | 8,000–15,000 | 100–250 | 200–500 |
| G02 | 1,800–3,200 | 3,600–6,400 | 0 | 0 |
| G03 | 800–1,500 | 1,600–3,000 | 100–200 | 200–400 |
| G04 | 700–1,300 | 1,400–2,600 | 350–700 | 700–1,400 |
| G05 | 500–1,000 | 1,000–2,000 | 200–400 | 400–800 |
| G06 | 600–1,200 | 1,200–2,400 | 1,600–3,000 | 3,200–6,000 |
| G07 | 500–1,000 | 1,000–2,000 | 150–300 | 300–600 |
| G08 | 1,300–2,500 | 2,600–5,000 | 100–200 | 200–400 |
| G09 | 1,000–2,000 | 2,000–4,000 | 150–300 | 300–600 |
| G10 | 700–1,400 | 1,400–2,800 | 900–1,800 | 1,800–3,600 |
| G11 | 1,800–3,600 | 3,600–7,200 | 0 | 0 |
| G12 | 1,400–3,000 | 2,800–6,000 | 0 | 0 |
| G13 | 0 | 0 | 200–400 | 400–800 |
| G14 | 0 | 0 | 200–400 | 400–800 |
| G15 | 0 | 0 | 100–200 | 200–400 |
| **残り合計** | **15,100–29,200** | **30,200–58,400** | **4,150–8,150** | **8,300–16,300** |

旧BE経路を全て完成させる場合の残りは素19,250–37,350行、補正後 **38,500–74,700行**。
検証済み18,959行を加えた計画値は **57,459–93,659行**。
BE適用を全部省いた場合も、一般部分の追加30,200–58,400行が残り、
既存分込み49,159–77,359行。どちらも承認された外枠を変更する数字ではない。
D81のHA基盤の実装費用をこの総計へ含めたり、この表で完成費用を見積もったことにはしない。

見積もりの根拠と限界：

- G01の素4,000–7,500は、§129の全付着1,500–2,600、標的への全延長1,800–3,400、
  向き・同じF≫U・HA表示の比較700–1,500の和。§129の3,000–5,200は最初の束だけであり、
  G01全体の残りではなかった。今回その後の二束も計上した。
- G02は重み付き極限・実準圏性・宇宙・全作用の比較が未着手。G03–G05はその上の全関手と
  全分裂を構成する量。既存の厳密bar326行、元の随伴、検証済みwalking sourceは再加算しない。
- G06の大きいBE部分は任意のnative U-split図式の実現の橋。D81により実現側が止まったという
  mainの方針の下で、③-bから無償で供給されるものとして差し引かない。
- G08–G09は同じcanonical比較の全Hom・実解像度による検収。ordinary Barr–Beckやh圏の結果で
  費用を0としない。G10は濃度と元のnative図式への比較、G11–G12は未実装の一般構成。
- G13–G15の一般部分は既存の同値移送・定義を使えるため0とした。BE部分の数値は
  元のBと宇宙・U・欄との照合であり、一般の移送定理を新造する費用ではない。
- 補正はユーザー指定どおり一律2。旧G01–G03の上端3,200に対し18,959行でもG01未完という
  実績から、係数2が安全な上端を保証するとはいわない。今回は残る作業を個別に積み直した素の値へ
  2を掛けた。G02以降は外挿が大きく、前提の新たな欠落が見つかれば再見積もりが必要。
- 各行は逐次再利用を前提とする。一般で構成したEM・bar・同値・accessibilityをBE側でも
  作り直す二重計上はしない。BEの0は特殊化が可能になった場合の追加構成0で、現在の完成を意味しない。

### 131.4 D81の下での要否

一般のG01〜G12はモナド理論として再利用可能だが、HAのCAlgのsifted保存・presentabilityを
示すために全部が必須というわけではない。HA 3.2.3の道なら、EM比較の完成を通らずに済む。
G13〜G15と、G01・G03〜G10のBE固有の右欄は、BEを採用・比較するという判断に依存する。
HA流のCAlgがBSの定義なら、旧`barrattEcclesCore`のpresentability欄を埋めることは
それ自体ではBSのHA-CAlgのpresentabilityを証明しない。逆向きも整流の同値なしには読み替えない。
整流を残す場合は、その同値・Uとの全比較はこの旧G12の適用表の外にある別の費用である。

## §132 5a-4・S7の入力を、G12全体を通らずに得る道の比較（紙）

### 132.1 欲しい入力を分離する

5a-4の保存の型は、既存SiftedColimitPreservation.leanの
`PreservesSmallSiftedColimits U`。すなわち全小sifted Kと元のnative図式・指定余錐cについて
`IsColimitCone c → IsColimitCone (mapJoinCocone U c)`。
この保存条件だけは余極限の存在を主張しないので、利用側が必要とする
`HasSmallSiftedColimits (CAlg)`も別に供給する。

S7については、小さいsite(C,J)と任意のCAlg値前層F、指定層化L_C・L_D、
後合成U_*、L_Cの同じ単位η_Fについて、少なくとも次を供給する必要がある。

```text
IsSheaf J F ↔ IsSheaf J (U_* F)
IsInvertibleEdge (mapEdge L_D (mapEdge U_* η_F)).toTruncated
FunctorIso (U_* (L_C F)) (L_D (U_* F))
VertexIso (U (RΓ_CAlg F)) (RΓ_D (U_* F))
```

上から二番目が未供給の単位条件。三番目はその単位に適合する比較であり、
単なる対象ごとの同値の選択で終えない。draftの二重層化の型は、U_* L_C Fが既に層であることと
合わせてこの比較へ結ぶ。最後は対応する全図式・指定極限錐も比較する。
D(A)のpresentability・層化の存在はG3・S1〜S6等の一般入力として別に要る。
CAlg側も、層化の存在はHA側で構成するか、指定反射を実際に作る必要がある。
極限の存在はHA 3.2.2.5とD(A)の極限から得る道もあり、G12全体を経由する必要はない。

### 132.2 候補の比較

| 道 | 原典・使う部品 | 5a-4への届き方 | S7への届き方・残る条件 | D81下での判断 |
|---|---|---|---|---|
| A：HAのCAlgで直接、operadicなsifted余極限 | HA 3.2.3.1・Cor 3.2.3.2、極限3.2.2.5、保存性3.2.2.6。必要ならpresentabilityは3.2.3.5 | D(A)^⊗の同じtensorがsifted余極限と両立することから、CAlg(D(A))の存在・保存・検出を直接検収 | それだけで単位条件を済ませず、下のA-S（monoidalな層化）かC-S（具体的反射の反復）を追加 | **HA定義に合わせる第一候補**。G01〜G15のモナド経路は不要。ただし∞-operad・対称モノイダルD(A)は実前提 |
| B：HA 4.7のBarr–Beckを直接 | HA 4.7.3.3–5、4.2.3.5、RV 6.3.8・7.2.7 | 指定比較の同値と、Tがsifted余極限を保つことが別に得られればEMの創出からUへ戻す。G10〜G15の全presentabilityは省略可能 | 反射L_DとTの両立、または代数的な層化を別証明し、単位比較まで作る | **G12全体の回避だが、G01〜G09の回避ではない**。保守性と随伴だけでは足りず、U-split実現条件を入力に要する |
| C：filtered保存＋幾何学的実現からsiftedへ | HTT Cor 5.5.8.17。Kerodon 9.7.2.1 (02QE)、9.7.2.9 (02QN)、9.7.2.10 (02QP)で形状を確認 | native filtered保存・全実現保存を先に証明して適用。HTTの同系の前提である始域の全小余極限の存在も要確認。ordinary sifted性は代用不可 | C-Sの反射の反復を使うなら、sifted全部よりfiltered鎖の保存が使える。ただし層化の構成自体を検収する | モナド・EMは不要だが、現在止まっている実現の橋が残る。5a-4のためにこの道を無条件再開とはしない |
| D：既存の`cAlgForgetDerived_mapJoinCone_isLimit`から延長 | 既存BEの実自由忘却随伴、HA 3.2.2.5の極限保存に対応。HA側には同じ形の極限定理を別実装 | 極限保存は余極限保存を結論しない。これだけでは5a-4へ届かない | 錐の像の極限性、既に層である前層のRΓ比較には使える。任意Fの単位の局所同値はなお必要 | **単独では不足**。CAlg値の錐の存在・層条件の反映・単位条件を補ってC-SまたはA-Sへ |

Kerodonの上記siftedの節は形状・対角・cofinalityの一般部品を供給する。
02ENも02QDも、BEの忘却やCAlg層化の単位を直接扱う定理ではない。
今回照合した節に、HAのBarr–Beckをそのまま置き換えてBEへの全適用まで済ませる定理を
確認したとは報告しない。番号の未確認な「Kerodonのモナド定理」を架空の近道として使わない。
本体のSiftedContractibilityとSiftedCoherentProductComparisonは、弱可縮性・空間の積比較の部品。
それらは任意の代数の忘却のsifted保存を既に証明した宣言ではない。

### 132.3 A-S：HAの対称モノイダルな層化で単位を作る候補

D81に合わせた候補は、P(C,D(A))の点ごとの対称モノイダル構造と
D(A)値の層化L_Dから始める。追加で証明すべき条件は、局所同値のtensorに対する閉性：

```text
∀ (f : X → Y), IsEquivalence (L_D f) →
  ∀ M, IsEquivalence (L_D (f ⊗ id_M))
```

これはHA Definition 2.2.1.6・Example 2.2.1.7の適合条件。
これを証明してProposition 2.2.1.9のモノイダル局所化を作り、
CAlg上の反射と、台が局所対象である代数の全部分圏を同定する。
さらに`CAlg(P(C,D(A))) ≃ P(C,CAlg(D(A)))`の全関手・評価との比較を構成する。
得られる反射の単位の台はL_Dの単位なので、S7の必要な反転性を直接検収する、という経路である。
この最後のCAlg・前層の比較と単位の同定は今回の推論による作業仕様で、
HA 2.2.1.9がS7全体をそのまま述べると引用しているのではない。

層のtensorは一般に点ごとのtensorをそのまま使うのではなく、必要な局所化を施す。
またS5の完全性だけから上のtensor適合性は出ない。
層化を反転する辺の生成系と、各Mとのtensorによるその閉性を示す必要がある。
この適合性・前層の代数の同定まで作れれば、EM準圏とBarr–Beckを通らずに
任意FのCAlg層化の単位条件へ届く。HA基盤の供給後の候補であり、今のBEコードへの即適用ではない。

### 132.4 C-S：極限保存＋filtered保存を用いた具体的層化の候補

HTT 6.2.2.7の証明（6.2.2.8以降）の被覆・右Kan・反復による層化を参照して、
同じ小さいsiteでCAlg値とD(A)値の反復を比較する道もある。
各段の被覆篩上の極限、被覆の細分によるfiltered余極限、十分長い反復鎖の余極限について、
存在・Uの保存・指定射の比較を全関手として構成する。
Uがそれらを保つと証明できれば、元の単位も反復を通じて比較できる。

ただしHTTの空間値の構成を任意の係数準圏へそのまま代入して済ませない。
CAlg側の反復が実際に層化の反射を与えること、濃度による停止、指定のČech層条件、
全前層に関する自然性を示す必要がある。hypercompletionへの置換もしない。
この証明にはBEの全presentabilityを先に完成させない余地はあるが、
filtered保存・必要な極限と余極限の存在のnativeな橋が追加で要る。
`cAlgForgetDerived_mapJoinCone_isLimit`はこのうち既に存在する極限錐を写す部分だけである。
CAlgの任意の極限を作ることや、層化単位の反転性を同宣言から無条件に取り出さない。

### 132.5 数学的な循環を避けた判断

- D81のBS本経路にはA＋A-Sを最初に検討するのが自然。
  HA 3.2.3.2による5a-4の主張と、HA 2.2.1.9を使うS7の単位の構成を分ける。
  HAの基盤の費用・担当は別の決定を要し、今回この経路を実装済み・承認済みとはしない。
- BはG12のaccessibility・全小余極限・BE欄の完成を省く候補にはなるが、
  G01とG06を含むモナド性の前提を消さない。5a-4の全sifted保存を先に仮定してG06を示し、
  そのBarr–Beckから同じ保存を出す循環は不可。Tの保存も自由Fが左随伴という事実だけでは出ない。
- CとC-Sはモナドを使わない対案。D81でBEを計算に残すなら比較の材料になるが、
  strictな図式の像の結果を任意native入力に読み替える橋、ordinary filtered保存との橋は残る。
- Dだけを使う場合、既に層であるFのRΓの比較までは候補だが、
  任意FのS7をそれへ縮めて完成とはしない。保守的な右随伴・極限保存だけでは単位条件は証明されない。
- G12を回避してS7を作るには、CAlg側の反射を別途実構成するか、HAのpresentabilityを
  3.2.3.5から得て一般の層化を適用し、さらに単位条件を上記の道で検収する。
  旧BE-G12が不要になることと、層化の存在・単位条件が不要になることは別である。

### 132.6 今回の検収・停止

G01の残りとG02〜G15を一般／BEに分けた型つき一覧、各々の素・係数2・合計は§131。
5a-4・S7の必要な入力、原典番号つきの候補と不足・循環は§132。
新しいLean宣言・一覧ID・完成項目は増えていない。
報告の数値は区間の加算と係数2を再計算し、diffの空白検査を行う。
対象ビルド・大きい監査・小さい公理監査はいずれも行わない。

G12：**一覧：済み 0／全体 15（うち追加 0）**。18,959／20,000行、Lean凍結を維持。
M15：**一覧：済み 10／全体 43（うち追加 1）**。5∞-2待ちを維持。
本報告を自枝にコミットして今回の紙の作業を止める。
