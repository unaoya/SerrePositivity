# F3受領後のBS実装計画

2026-10-14。BS主計画§41の実行順と受入条件。
原典は著者公開版Lemma 2.18、Prop 7.2、Lemma 3.9、Theorem 3.10、Cor 7.3。
担当はBSチャット。共通基盤・CLMSTの所有ファイルを編集しない。

## 受領したもの

公開入口：`HomologicalAlgebra/DerivedCompletion/PDCompletion.lean`。
任意の可換環A、自然数p、d:Aについて、p正則性・Noether性・ねじれの有界性を要求しない。

- `PDCompletionH0 A p d`は元の二座標Koszul完備化複体の実際のH⁰。
- `pdCompletionCommRing`、`pdCompletionAlgebra`はその環・代数構造。
- `pdCompletionUnit`は標準環射。`pdCompletionUnit_apply`は元の複体の標準H⁰写像との一致。
- `pdCompletionH0_isComplete_p/d`は標準射によるA作用の下での実導来完備性。
- `pdCompletion_existsUnique_ringHom`は、g:A→TによるA作用の下でTがp,d導来完備なら、
  H⁰→Tの唯一の環射で標準射からgを延長するものが存在するという普遍性。
- `pdCompletionObject_isComplete_p/d`は実導来対象側の完備性。
- `pdCompletionIteratedEquiv`と`_unit`は一座標反復との比較と標準射の図式。

BS側で対象ビルド（2422ジョブ）と全14公開宣言のassert_no_sorry・公理依存を再確認した。
公理依存はpropext・Classical.choice・Quot.soundのみ。
一般の古典的(p,d)完備化と同一視した結果ではない。

追加受領済みAPI：`ScalarRestriction.isModuleComplete_algebraMap_iff`、
`isModuleComplete_ringHom_comp_iff`、別座標の完備性の保存。
N4時点で不足に含めた係数制限のこの部分は再実装・再要求しない。

## 実装順

| 順 | 工程 | 主な成果 | 完了判定 |
| --- | --- | --- | --- |
| P1 | F3のBS側での作用・型の接続 | H⁰自身のp,j(d)導来完備性、標準射の利用 | 既存型のまま公開補題と監査 |
| P2 | W₂の具体的加群構造と完備性 | 切断延長に必要なW₂(H⁰)の導来完備性 | ねじれ作用と短完全列を証明 |
| P3 | H⁰へのδ延長 | 具体的δ構造、標準δ射、一意δ延長 | 一般δ基底・pねじれを許す公開定理 |
| P4 | 原典の一段操作 | 除算添加→旧ねじれδ閉包商→実H⁰ | 具体的標準射と試験δ環への一意延長 |
| P5 | δ余極限・反復・最終正則性 | 原典のsuccessorと極限段、最終d正則性 | 宇宙・等式検出・共終性を証明 |
| P6 | 最終完備性と試験prismへの接続 | 最終prismとProp 7.2の始対象性 | ω₁比較・Lemma 3.5/4.8の一般形 |
| P7 | B2との合流 | 完全prism化→IsPerfectoidization | F4〜F7の利用型と一般B3の公開定理 |

まずP1〜P3を最初の実装区切りとする。各工程で個別コミットする。
P4以降までをF3受領だけで完成できるとは約束しない。

## P1：既存のH⁰をそのまま使う

予定ファイル：`BhattScholze/PDCompletionInterface.lean`。
A:Type u、素数p、d:A、H=PDCompletionH0 A p d、j=pdCompletionUnit A p dとする。
既存の環構造を局所インスタンスに置き、H自身の作用による
IsModuleComplete H (p:H) (ModuleCat.of H H)と
IsModuleComplete H (j d) (ModuleCat.of H H)へ係数制限比較を適用する。

試験射g:A→Tの普遍性も、必要な場合だけT自身のp,g(d)完備性へ接続する。
同等の新しい完備化型・完備性定義・一般比較補題を作らない。
標準射の像の公式と、実際のH⁰写像である証拠を維持する。

## P2：W₂短完全列とねじれ作用

予定ファイル：`BhattScholze/WittTwoModuleSequence.lean`、
`BhattScholze/WittTwoPDComplete.lean`。一般Witt APIは既存の共通層を再利用する。

D:DeltaStructure p Aに対し、A→W₂(H)はW₂(j)∘D.sectionHom。
この射によるA作用の下で、原典の短完全列
0→φ*H→W₂(H)→H→0を具体的に構成する。
左項は第1座標の加法群で、r:Aの作用はj(D.frobeniusLift r)倍。
標準A加群Hと同一視しない。第0座標射・核への射・加法と作用・exactnessを検証する。

φ(p)=p、φ(d)=d^p+pδ(d)を使い、p,dについての完備性から
p,φ(d)についての完備性を供給する比較が必要。
イデアル(p,d)と(p,φ(d))の冪の包含を確認し、一般導来加群比較が不足する場合だけ
その正確な型を主計画の共通要求に追加する。未証明の根基不変性を仮定しない。
既存ModuleClosure.isModuleComplete_extensionでW₂(H)の完備性を得る。

## P3：実際のH⁰へのδ構造の延長

予定ファイル：`BhattScholze/DeltaPDCompletion.lean`と、必要なら
`BhattScholze/DeltaPDCompletionUniversal.lean`。

P2の完備性を使い、F3の環普遍性からs:H→W₂(H)を構成する。
第0座標との合成がid_Hであることを、標準射上の一致とF3の一意性から証明する。
sを切断とするDeltaStructure p Hを定義し、jがδ射であることを証明する。

公開普遍性の入力：δ環(E,T)、g:A→Tはδ射、T自身がp,g(d)について導来完備。
出力：一意なδ射h:H→Tでh∘j=g。
環としての一意性を再利用し、δ性はW₂への二つの射を比較して証明する。
P2で試験環側のW₂完備性も供給する。p正則性を追加して一般命題を弱めない。

原典Lemma 2.18の完備化への適用部分を目標とし、一般étale持上げの新規構築へ広げない。
最初の到達点はこのδ普遍性。prism性やIsPerfectoidizationはまだ結論しない。

## P4：一段操作

予定ファイル：`BhattScholze/DeltaDivisionPDCompletion.lean`。
既存DeltaDivisionTorsionQuotient D d aをUとし、d_Uの実PDCompletionH0を使う。
P3でδ構造と標準射を構成し、既存除算・ねじれ商の普遍性を合成する。
試験条件はδ基底射f、f(d)正則、全f(a_s)のf(d)可除性、p,f(d)実導来完備性。

dがdistinguishedなら標準δ射により像もdistinguished。
完備化後のd正則性は仮定も結論もしない。一段の完備化が新ねじれを作り得るため、
P4完了をProp 7.2のprismの存在と数えない。
既存ClassicalDeltaDivisionCompletionは維持し、この実H⁰へ無条件には同定しない。

## P5〜P7：残る条件と並行して進められる部分

詳細は`Prop72Construction.md`のsuccessor・極限・安定化・宇宙・試験対象の記録。
P3/P4の型が確定した後、δ有向余極限と有限等式の後段検出を実装する。
各段のdねじれが後続のねじれ除去段で消えることから、最終d正則性を導く。
全段のd正則性・遷移射の単射性を仮定しない。

F3本体に含まれない残件：ω₁-filtered余極限での実導来完備性の保存、または
その余極限と完備化の比較。固定基底とp,d、共終性条件、標準射の図式を明示する。
この一般加群比較は共通基盤への追加要求であり、F3本体の未受領とは呼ばない。
δ余極限・torsion-killing・d正則性はBS担当で、比較を待つ間も独立に進められる。

Lemma 4.8の任意perfectoid環から非完全prismへの一般持上げ、
Lemma 3.5の一般試験対象への適用もBSの未完了工程。
既存の完全prism間のHom定理やp正則な試験対象だけの定理で代替しない。

一般B3への接続にはB2の一般対応も必要で、F4〜F7は引き続き待合せ。
B4の全射性、B5のmod p^N冪等性、André入力、B-I/B6は今回の最初の区切りに含めない。
N3の標数p特殊場合のIsPerfectoidizationは独立した証明済み成果として維持する。

## 検証と停止条件

各工程：対象ビルド、全公開宣言のBS専用assert_no_sorry・公理依存・import閉包監査、
区切りで全体ビルド。自分の変更だけを個別コミットする。
新しいsorry・公理・外部引用と既存存在/全射性引用への循環依存は追加しない。

P2で一般完備性比較が不足しても、具体的W₂短完全列とP1は完成させて正確な不足を記録する。
不足した補題だけを待ち、関係のない工程は停止しない。他チャットへの送信は行わない。
受領済みF3の実装をBS側で作り直さない。
