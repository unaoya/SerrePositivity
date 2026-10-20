# E∞-dg 代数

## 規約

namespace は `SerrePositivity.EInfinity`。
`A : Type u`、`[CommRing A]`、`Complex A = CochainComplex (ModuleCat.{u} A) ℤ`。
複体は非有界、微分は +1、ホモトピーは −1。
射影モデル構造は `letI := projectiveModelCategory A` として局所的に選ぶ。
対称列は既存の `SerrePositivity.SymmetricSequence (Complex A)` を使う。
その共変な置換作用から、逆元で通常の右作用を得る。
テンソル積と交換には既存の Koszul 符号付きモノイダル構造を使う。
オペラッドと代数は arity 0 の演算を含む。

## E2a-3 の採用方針（2026-10-19）

目標は任意の可換環 A 上の完全な転送モデル構造であり、
弱同値と fibration は忘却関手 U で作る。自由関手を F、複体の生成類を I・J とする。
`Transfer.Right.rightTransfer` に渡す acyclicity は次の包含である。

```text
transfiniteCompositions ((coproducts (J.strictMap F)).pushouts)
  ≤ (quasiIso (ModuleCat A) (.up ℤ)).inverseImage U
```

原指示の Berger–Moerdijk §5 の filtration 議論では、命題 5.4 の入力の代数は
cellular である。Berger–Fresse 3.1.7 も Σ-projective なオペラッドに対する
cofibrant な始域の結論を述べている。これらから任意の始域に対する上記の包含を
そのまま得ることはできない。始域の cofibrancy を追加した結果で置き換えない。

採用する証明経路は次の四工程とし、各工程で検証してコミットする。

1. **Hopf 構造**：各 `E(n) = N_*(EΣ_n)` に Alexander–Whitney 対角を構成する。
   一般の単体集合について shuffle 写像が AW 余代数の射であることを証明し、
   単体的合成写像に対する AW の自然性から `E → E ⊗ E` のオペラッド射性を得る。
   余結合性、augmentation `E → Com` による余単位、Σ_n 同変性も証明する。
2. **区間の界面**：E-coalgebra H、鎖ホモトピー同値である余単位 `H → 𝟙`、
   E-coalgebra 射であり次数ごとに分裂単射である二点 `𝟙 ⊕ 𝟙 → H` を
   一つの structure にまとめる。この界面から全 E 代数の functorial path object
   `A → Hom(H, A) → A × A` を構成する。
   fibration に対して左持ち上げ性を持つ代数射について、終対象への持ち上げから
   retraction を得て、path object の両端への fibration に持ち上げることで、
   底の複体射がホモトピー同値であることを証明する。
   これにより `fibrations.llp ≤ weakEquivalences` を得る。
   自由・忘却随伴の lifting 対応から J-cell 射の acyclicity を導く。
   自由像の I・J の小対象性と有限極限・余極限も証明し、
   `Transfer.Right.rightTransfer` の適用を H の具体的構成に依存せず閉じる。
3. **区間の構成**：`H = N_*(Δ¹)` を用いる。Berger–Fresse §1.3 の
   table reduction `TR : E → χ` のオペラッド射性を一般に証明し、
   χ の区間切断作用（McClure–Smith）を Δ¹ に適用する。
   区間切断作用の計算は Δ¹ に特殊化してよく、必要な次数は `E(n)_r, r ≤ n`。
   一般の単体集合への一般化は費用が変わらない場合に限る。
   着手前にファイル数と主要補題の見積もりを計画に一段落で記す。
4. **転送の完成**：構成した区間を工程 2 の界面に代入して E2a-3 を完成し、E2a-4 へ進む。

四工程は完了。`IntervalCuts.coalgebraInterval` は実際の正規化区間を用い、
`BarrattEccles.modelCategory` は任意の可換環上の完全な転送モデル構造を与える。
モデル構造は局所的に選び、`BarrattEccles.forget_isRightQuillen` も追加仮定なしに使える。

この経路は Berger–Moerdijk 命題 4.1・§4.6.3、Berger–Fresse §3.1 に基づく。
始域の cofibrancy は追加せず、任意の可換環上の完全なモデル構造を構成する。
Hinich 4.1.1 はこの工程の原典に用いない。正標数では E は Σ-split でないためである。

工程 1 は完了。一般の正規化 AW 鎖対角と shuffle の余代数射性を整数模型へ移し、
`BarrattEccles.partialComposition_diagonal_tensorμ` で既存 BE 部分合成との両立を検証した。
`Operad.hadamard` は arity ごとのテンソルオペラッドであり、単位・内外等変性・
入れ子と独立な代入の結合則を含む。`BarrattEccles.unit_diagonal` と自然性を合わせ、
`hopfDiagonal : E → E ⊗ E` を実際のオペラッド射として構成済み。
`BarrattEccles.hopf` はこの対角、既存の `augmentation : E → Com`、
余結合性と左右余単位則を束ねる。余可換性は要求しない。
工程 2 の抽象界面は `Operad.CoalgebraInterval`。余演算を保つ二端点・収縮と、
底の複体の境界 cofibration・収縮の擬同型を持つ。区間は augmentation を保存する
オペラッド射で制限でき、制限射の Hopf 対角保存は不要。
`convolutionAction` は内部 Hom 上の各 arity の演算 chain map、
`CoalgebraInterval.prepathComplex` は底の複体の定数射・両端点評価と三角形を供給する。
定数・評価の自然性も検証済み。`convolutionAction_unit` が単位則、
`convolutionAction_equivariance` が全置換についての等変性を与える。
`convolutionAction_post` は P 代数射による後合成の演算保存を与える。
反復評価は二ブロックの連結・分割と両立する。
`convolutionAction_insertion_zero_evaluation` は標準の先頭代入と余代入の評価を比較する。
`Algebra.ofFirstComposition` は等変性と先頭の部分合成則から全代数公理を構成する。
`convolutionAction_comp` で全位置の部分合成則を証明し、`convolutionAlgebra` を構成済み。
余代数射の前合成も全演算を保存する。`convolutionFunctor` は固定した余代数からの
代数の自己関手、`convolutionPreNat` は余代数射による自然な前合成を与える。
`unitCoalgebra ε` は任意の augmentation からの単位余代数。
`convolutionUnitNatIso` は Hom(単位,B) ≅ B を自然な代数同型にする。
`CoalgebraInterval.prepathAlgebra` は自然な代数射である定数射・両端点評価を持ち、
底の射は既存の `constant`・`evaluation` と厳密に一致する。
`evaluationPair_projectiveFibration` は底の二端点評価の対の射影 fibration 性を与える。
射影 cofibration の各次数での分裂を持ち上げ性から導き、任意の値域への Hom の
境界制限の全次数全射性を証明した。値域の cofibrancy は不要。
`constant_quasiIso` と `evaluation_quasiIso` により、定数射と両端点評価は底で擬同型。
単位の cofibrancy と端点の trivial cofibration から鎖ホモトピー逆を構成し、
符号付き前合成によって内部 Hom へ移した。区間のホモトピー同値性を追加仮定にしていない。
`Algebra.ofJointlyMonicActions` は共同単射な射の後で代数公理を判定する。
`Algebra.binaryProductIsLimit` と `Algebra.terminalAlgebraIsTerminal` により二項積と終対象を構成。
`Algebra.binaryProductIso` は選んだ積と底の直和上の代数の比較同型。
弱同値・fibration の構造は忘却の逆像として局所的に選び、モデル構造は仮定しない。
`CoalgebraInterval.pathAlgebra` は全代数の good path object。
`fibrations_llp_quasiIso` は終対象と二端点評価への持ち上げから retraction と逆合成の path を取り、
底の擬同型性を示す。`freeGeneratingTrivialCofibrations_cell_acyclicity` は自由・忘却随伴と
左持ち上げ類の閉性を使い、任意の始域に対する相対 J-cell 射の acyclicity を与える。
`Algebra.forget_createsLimit` は任意の底の極限錐を頂点ごと持ち上げる。
代数の圏は全ての小極限を持ち、忘却は底に存在する形の極限を作り、保存する。
`tensorPower_preservesSiftedColimits_of_tensor` は一般のモノイダル圏で両変数の保存から
有限テンソル冪の sifted 余極限保存を導く。複体の閉モノイダル構造へ適用済み。
Schur 関手と自由・忘却の合成の sifted・filtered 余極限保存も検証済み。
工程 2 は完了。`Algebra.forget_createsColimit` はテンソル冪で保存される底の余極限を作る。
sifted・filtered 余極限の創出・保存と忘却のモナド性を証明済み。
reflexive coequalizer の形の sifted 性を検証し、図式圏へのモナド性の拡張と随伴持ち上げで
代数の全小余極限を構成した。一般の余極限を忘却が保つとは仮定しない。
自由代数による有限表示性の保存から、自由像の I・J が ℵ₀ の小対象論法を許すことを証明。
`Operad.intervalModelCategory` は任意の Hopf オペラッドと余代数区間からの完全な転送モデル構造。
弱同値と fibration は忘却の逆像であり、自由像で生成され、忘却関手は右 Quillen。
モデル構造は局所的に選び、始域の cofibrancy は要求しない。
工程 3 は TR の正規化への降下まで構成済み。`Surjection.BasisWord` は隣接値が異なる全射語、
`degreeModule` はその自由加群であり、退化・非全射な語は零へ送る。
区切り位置の個数が次数に等しいこと、削除符号と線形な削除写像の置換同変性を証明。
次数零は置換と同値で、BE の右作用の規約には逆置換の語が対応する。
原典の七文字の例の符号・五項の削除式と、arity 0 の空語を監査で照合済み。
`TableReduction.onSequence` は任意の次数・arity の置換列について行長の有限和を構成する。
行抽出の長さと単射な文字変更との両立、有限和の置換同変性を証明済み。
`degreeMap` は実際の BE 複体の自由基底から各次数の線形写像へ延長する。
次数零は逆置換の語、arity 0 の次数零は空語・正次数は零になる。
原典の table の例について、非退化出力の二項と各項の重複度 1 を監査で確認済み。
同じ隣接行の境界重複から、退化な置換列の各項と有限和の消滅を証明済み。
`onSequence_eq_zero_of_degenerate` は実際の BE 退化単体の消滅を与える。
`normalizedMap_generator` は退化単体も含む全ての正規化生成元の像を table の和と同定する。
`degreeMap_action` は実際の BE 各次数の線形写像の置換同変性。
`canonicalRow` は確定した最終出現と残りの最初の出現を連結し、全値を一度ずつ含む。
`canonicalPermutation` はその行を BE の頂点置換に変換する。
`rowStart` は区切りから得る d+1 個の開始位置で、狭義単調かつ正の arity では終端より前。
`canonicalVertices` と `canonicalSimplex` は指定した全射語の逆像候補を構成する。
復元行は最終出現だけの区間では不変で、区切りでは一文字を非自明に後方へ移す。
開始位置と次の区切りの間には別の区切りがないことを証明し、実際の隣接頂点へ適用済み。
`canonicalSimplex_mem_nonDegenerate` は候補単体の非退化性、
`canonicalNondegenerateSimplex` は正規化 BE 基底の実際の添字を与える。
`canonicalRows_force_length` は正しい先行除外から非退化に抽出できる行長を cut−start+1 に強制する。
`canonicalRows_extract_original_segment` と `canonicalRows_exclusion_update` は、
その長さで元の語の一行を抽出し、次の正しい除外状態へ移ることを保証する。
最後の行の尾部は重複せず、`reduceRows_canonical_last` で残りの語全体を抽出する。
`canonicalSchedule` は正しい全行長で、`reduceRows_canonical` はその抽出が元の語と証明する。
`schedule_eq_canonical_of_isChain` により、非退化出力を持つ Schedule はこれだけである。
`onSequence_canonical` は nullary を含む全 arity で標準頂点列の TR が元の語となる式。
`degreeMap_comp_section` は各次数の線形な切断、`degreeMap_surjective` と
`normalizedMap_surjective` は任意の可換環・全 arity・全次数での全射性を与える。
この切断が微分や部分合成を保つとは主張しない。
`differential_generator` と `differential_listGenerator` は退化・非全射な語も含む削除和の式。
隣接同値の二つの削除は逆符号で相殺し、他の削除は退化のまま残ることを証明済み。
TR の微分と BE 頂点境界を別々の有限和に展開し、微分保存との必要十分条件を構成。
nullary 境界恒等式を含む一般の微分保存は `normalizedMap_comm` で証明済み。
`reduceRows_delete_singleton` は一文字行の削除による出力の一文字削除を与える。
`scheduleTransfer` は相殺相手の行長の候補で、総和・正値性・上界と自然数値の逆移動を検証。
`ExtractionTrace` は成功した抽出の各行と除外状態を保持する。
各行の末尾以外は後続に現れず、長さの上限が飽和することから非最終行末の再出現を証明。
`rowEnds_of_reduction` は再出現位置が非最終行末に尽きることを与える。
`rawRowEndSigns_of_reduction` は退化出力も含む全成功 table で、その削除係数を (−1)^行番号と同定する。
`rowEndOffsets_of_reduction` は区切り位置を Schedule の行長の部分和−1 と表示する。
`singletonScheduleEquiv` は指定位置の一文字行の削除・挿入を次数間の全単射にする。
`singleton_boundary_certificate` は一文字行の削除位置・出力・符号を同時に与える。
最終一文字行では出力末尾が隣接重複し、その係数は直前行末の符号反転で頂点境界と一致する。
`singleton_reduction_none_iff` は元の table と頂点削除後の抽出の失敗が同値であることを示す。
`singleton_deletion_term` は任意の可換環で符号付き削除項と頂点境界項の値を同定する。
`sum_singletonSchedules_vertexBoundary` は Schedule の全単射による有限和を頂点境界と同定する。
`rawListDifferential_eq_sum` は退化・非全射な出力も実際のリスト位置の削除項の和にする。
`scheduleOffset_strictMono` は行の開始位置の単射性を与える。
`singletonPositions` で一文字行の削除位置を取り出し、補集合を `remainderTerm` と定義した。
`differential_onSequence_vertexBoundary_add_remainder` は TR の微分を頂点境界とその残余和に分ける。
`normalizedMap_comm_iff_remainder_zero` は実際の BE 正規化写像の微分保存と残余和の零性の同値。
`output_position_owner` は全ての出力位置の所属行・行内位置・開始位置・行の重複のなさを与える。
`final_deletion_rows` は残余の最終出現削除について、削除行と直前の同値の出現の先行行を特定する。
二行の順序、削除行の長さ 2 以上、受け取り側の arity の余裕、行番号による削除係数を証明。
`deletionScheduleTransfer` は受け取り側の余裕を全体の行長から導き、逆移動が元へ戻ることも保証する。
`reduceRows_congr_removed` は除外の順序によらない抽出の一致。
`reduceRows_donor_step` は削除値を早く除外して短くした行の出力を計算し、元の後続抽出へ合流させる。
`ExtractionPrefix` は元の抽出の先行部分の選択行と終端の除外状態を保持する。
`ExtractionPrefix.append_early_exclusion` は削除値のない任意個の中間行を、早い除外を保って通過する。
`receiver_capacity_of_tail` は後続の別の値から、受け取り行の利用可能長の実際の余裕を導く。
`reduceRows_receiver_step` は長くした受け取り行の出力と削除値の早い除外を計算する。
`transfer_block_deleted_outputs` は三部分の抽出を連結し、指定した一文字の削除後出力の一致を証明する。
`previousOccurrence_not_mem_slice` は直前の同値の出現と削除位置の間に削除値がないことを示す。
`rows_deletionScheduleTransfer` と `rows_transfer_blocks` は実際の Schedule の二行だけを変更することを示す。
`two_row_extraction` は元の成功抽出を先行部・二行・中間部・後続の状態と出力へ分ける。
`final_deletion_location` は削除行の指定に実際の削除位置の所属範囲も保持する。
`final_deletion_row_cases` は最終出現の削除を行内部か最後の行末に分類する。
`terminal_transfer_block_deleted_outputs` は最終末尾の削除にも成功抽出と削除後出力の一致を与える。
`ScheduleBlock` は一般の成功 Schedule の分割・状態・出力と開始位置を一つの証明書にまとめる。
`receiver_selected_end`・`donor_split`・`previousOccurrence_not_mem_middle` はその実際の語と不出現を導く。
`final_deletion_transfer` は前の同値出現を持つ残余の最終出現削除から、相手の Schedule の成功と削除後出力一致を構成する。
`final_deletion_pair` は相手の位置を新しい行末と同定し、逆符号と削除後次数 d−1 の正規化二項の相殺を与える。
最終末尾の例は、元の削除項が削除後次数零で非零であることも監査で照合する。
相手の位置が残余集合内の区切り削除となることも `final_deletion_pair` に保持した。
`residual_caesura_row` は全ての残余の区切り削除を長さ 2 以上の非最終行末として取り出す。
`reduceRows_released_donor_step` は除外を解いた値を後の行内へ挿入し、元の後続抽出へ合流する。
`ExtractionPrefix.finish_length` と `finish_nodup` は除外状態の実際の長さと重複のなさを与える。
`available_vertexRow_length_add` は利用可能長＋除外長＝arity、解放時は利用可能長が一つ増える。
`final_prefix_saturated` は元の成功 table の最終行が利用可能値を取り尽くすことを保証する。
解放値はその最終行の延長選択に入る。
`ReleaseSearch` は影響しない行を通過し、内部出現または最終延長で最初に停止する探索の証跡。
`releaseSearch_exists` は元の成功と除外予算から停止行の存在を導き、`ReleaseSearch.unique` は全分割・選択・終端状態の一意性。
`released_suffix_budget` は実際の Schedule から探索の予算を供給する。
`receiver_release` は現在行を一文字短くして直前値を解放し、初期の重複のなさと不所属を保証する。
`releaseSearch_constructs_extension` は停止行の延長による成功抽出と、一文字だけを挿入した後続出力を構成する。
`reverse_block_extraction` は現在行の短縮も連結し、二つの削除後出力の一致を与える。
`reverseTransferData_nonempty` は全残余行末から実際の逆 Schedule の成功と削除後出力の一致を構成する。
`ReverseTransferData.point_not_caesura` と `point_previousOccurrence` は挿入点の最終出現と直前出現の短縮行末を同定する。
`point_in_late_row` と `point_not_singleton` により挿入点は長い延長行内の残余位置。
`point_coefficient` と `pair_cancel` はその負符号と次数 d−1 の正規化二項の相殺を与える。
`forward_rows`・`forward_schedule`・`forward_position` は逆から順へ戻した二行・Schedule・位置の一致。
`ScheduleBlock.forward_release_search` は元の中間行を通って元の削除行で停止する逆探索を構成する。
`ScheduleBlock.reverse_search` と `reverse_result` は順から逆の解放値・二行・成功出力・削除位置を復元する。
`DeletionPoint` は退化出力も含む実際の成功削除点の有限型。
`deletionEquiv` は残余最終出現削除と残余区切り削除の全単射。
`sum_remainingValue_zero` は全単射と逆符号で全成功削除点の残余和を相殺する。
`sum_remainderTerm_eq_points` はその和を元の Schedule の残余和と同定し、
`sum_remainderTerm_zero` で全残余和の零性を追加仮定なしに証明した。
`normalizedMap_comm` は零 arity を含む全 arity・全次数の TR の微分保存。
`differential_comp_differential` は TR の全射性と微分保存から χ の平方零を導く。
`Surjection.normalizedChains` は実際の χ の鎖複体、`TableReduction.chainMap` は実際の TR 鎖写像。
`Surjection.OverlapPartition` は BF §1.2.4 の端点を重ねた部分語の長さによる有限分割型。
空語の分割は一出現の場合だけ存在する。`position_covered` と `value_mem_segments` で内側語の被覆を証明。
`compositeWord_length` と `compositeWord_surjective` は全合成語の正しい次数と全射性を与える。
`compositionExponent` と `compositionSign` は BF §1.2.5 の成分の行次数による Koszul 符号。
`compositionOnWords` と `Surjection.partialComposition` はその符号付き有限和の両線形延長。
次数零の符号は正、複数出現への空語挿入は零と検証した。原典 §1.2.6 の三つの語と符号 +,−,− を監査する。
`substitute_isChain` と `compositeWord_nondegenerate` は正の内側 arity の全合成語の非退化性。
`compositeBasisWord` と `compositeGenerator_eq_basis` は各正規化合成項を実際の基底に同定する。
`sum_segmentDegree` と `sum_outerSegmentDegree` は内側・外側の成分次数の和を e・d と同定する。
`sum_outerSegmentDegree_suffix` は後続外側次数を順位差で計算する。
`compositionPath` はこれらの成分次数の移動を連結した実際の d×e shuffle 経路。
`compositionPath_sign` はその実際の shuffle 符号が元の合成符号と一致することを証明する。
`permutationComposition_inverse_row_substitute` は実際の合成置換の逆置換行を一出現への代入に同定する。
`compositionRemoved` は内外ラベルの像から合成表の除外状態を作る。
`permutationComposition_available_substitute` は、指定値が未除外なら利用可能行も同じ代入と一致する。
`compositionStateRemoved` は指定値の最終除外後に全内側ラベルを除く状態へ拡張する。
`permutationComposition_state_available_substitute` は全段階で利用可能行と代入の一致を与える。
`compositionSelectedUpdate_before`・`inside`・`after` は選択語の末尾を残す実際の除外更新。
`compositionExtractionStep_before`・`inside`・`after` はこれを既存の `reduceRows` の成功分岐へ接続する。
内側 arity 零を含み、実際の合成置換の二行抽出で選択行末が次行にも残ることを監査する。
`ExtractionTrace.lineRank_schedule` は元の成功証跡の各行内で lineRank を行添字に同定する。
`reductionRow` は語の位置の実際の有限所属行。元の Schedule の行内区間で特徴付けられる。
内外成分次数は元の成功表の終行・始行番号の差と一致する。
`occurrence_reductionRow_strictMono` は同じ指定値の各出現が狭義に異なる行へ進むことを与える。
これらは退化した成功出力にも適用する。
`reductionCursor` は同じ元の成功から所属行直前の証跡・除外状態・利用可能行・列を取り出す。
`reductionCursor_composite_row` は元の具体的状態から実際の合成行の一出現代入表示を構成する。
`ScheduleRowCursor.next_state` は隣接する証明書の状態を元の末尾以外の除外更新で同定する。
`remainder_success_eq_drop` は行の途中から元の語のその位置以降を実際に抽出する。
`ReductionInterval` は任意の閉区間の実際の語・両端状態・正しい行数と元の連続する行を保持する。
`componentExtraction` は正の語長の全ての重なる分割成分の証跡で、実際の部分語を返す。
その行数は成分次数＋1。隣接成分の証跡は同じ共有端点の状態で厳密に連結できる。
同じ一行内の成分と複数行成分を同じ界面で扱う。空語の分割は従来どおり別途扱う。
`outerComponentExtraction` は指定値の出現境界で切った外側成分を同じ元の区間から抽出する。
`weightedVertices` は元の置換頂点と選択長さを保持し、行表示へ戻すと同じ成分行列になる。
`componentVerticalExtraction_success` は元の二つの成功から実際の垂直合成ブロックを任意の後続へつなぐ。
`rowFusion_of_success` は接合部の同じ二行を融合し、共有文字を一度だけ数えて元の終状態へ接続する。
`horizontalExtraction_success` は指定値が終状態で未除外の外側証跡を固定内側の実際の合成表へ移す。
`componentHorizontalExtraction_success` はこの水平転送を元の二つの成功表から直接構成する。
指定値を含む選択ではその値が末尾になり、内側の先頭一文字だけを使って残りを保持する。
`reductionRemoved_last_singleton` は元の最終行の飽和性から、最後の位置の一文字可用行を導く。
`finalHorizontalExtraction_success` はこの状態で指定値の最終除外を跨ぐ最終外側成分を転送する。
これにより正の内側語長で全種類の水平・垂直成分の実際の合成ブロック転送がそろう。
`rowFusion_in_context` は任意の先行部分の後でも共有行を融合し、正しい全出力の一文字削除へ移す。
`TableCompositionData` は元の二つの成功と重なる分割だけを保持し、合成成功を入力にしない。
`state_zero` で空の初期状態を確認し、`raw_success_zero` で全成分連結表の実際の成功を構成する。
この段階では各ブロック境界の共有行と共有文字をそれぞれ二つ残す。
`weightedVertices_vertex` は成分の全置換を元の連続頂点で評価し、始終置換も同定する。
`horizontal_vertical_join`・`vertical_horizontal_join` は両種類の境界での実際の共有行の一致。
各ブロックの行数は成分次数＋1であり、各行の非重複性も元の合成置換から得る。
`fuseBoundary_in_context` はブロックの共有境界行の一致を全表の実際の融合へ移す。
`fused_success_zero` は全境界を融合した行列が空の除外状態から実際に成功することを証明。
`boundaryEraseIndex_of_success` は融合で消す位置を各成功ブロックの出力の最終位置へ同定する。
`fusedWord_step` により融合出力は成分語だけで計算でき、成分行長の古典選択を展開しない。
`blockWord` は各水平・垂直語の dropLast と最後の水平語を連結する計算可能な出力表示。
`fusedWord_eq_blockWord` で実際の融合出力との一般の一致を証明し、
`fused_success_blockWord` で全融合表の出力を元の成分語だけへ同定する。
`substitute_append` は外側語の前半の指定値の出現回数だけ部分語を消費する連結公式。
`occurrenceAt_complete` は全ての実際の出現の列挙への所属、連続出現間・両端外の不出現を与える。
`occurrenceAt_count_take` と `occurrenceAt_count_take_succ` は指定出現の直前・直後の消費済み部分語数を同定する。
`substitute_at_occurrence` は任意の出現での代入を前半・挿入語・後半へ分解する。
`compositeWord_at_occurrence` はその挿入語を重なる分割の実際の同じ番号の成分へ照合する。
`firstHorizontal_dropLast` は最初の水平語の末尾を除いた部分を最初の出現以前の実際の代入へ戻す。
`middleHorizontal_dropLast`・`finalHorizontal_word` は中間・最終水平語も実際の代入へ分解する。
`verticalWord_append_endpoint` は垂直末尾を次の水平先頭で一度だけ復元する接続式。
`blockWord_after_occurrence` は共有先頭文字と元の未消費代入を後ろから全成分で照合する。
`blockWord_eq_compositeWord` は全成分語の実際の合成語との一般の一致。
`fused_success_compositeWord` は元の二表の成功と分割から、全共有行融合表の実際の合成語抽出を証明する。
`fusedRows_length` は全共有行融合表の行数が d+e+1であることを証明する。
`fusedRows_row_length` と `reduceRows_row_bounds` は各実際の選択長さの正性と合成 arity 以下の上界。
`fusedLength_sum` は実際の合成語抽出から総行長を同定し、`fusedSchedule` が既存の Schedule を構成する。
`rows_fusedSchedule_of_fst` は元の行列の一致から、Schedule を付けた実際の表の復元を与える。
`horizontalRows_fst`・`verticalRows_fst` は行列を元の連続する置換区間の部分合成として表示する。
`fusedRows_fst_step` は境界一行を省く同じ行順の再帰であり、経路の頂点列の連結と比較する。
`DegreePath.append_horizontal_front`・`back` と `append_vertical_front`・`back` は連結経路の実際の座標。
`DegreePath.vertices_append` は前半末尾を省き、平行移動した後半を付ける全頂点の公式。
`vertices_horizontal`・`vertices_vertical`・`vertices_corner` は各純粋成分の連続座標列。
`DegreePath.blockVertices` は計算可能な成分次数からの座標列で、`vertices_blocks` が実際の経路と同定する。
`compositionPath_vertices` は実際の全経路の頂点列を同じ成分座標列へ戻す。
`overlap_append`・`fuseBoundary_fst_dropLast` は共有右先頭の削除を左末尾の削除へ移す。
`outerGrid`・`innerGrid` は元の有限所属行と一致する自然数座標で、上界と次数による更新を証明する。
`rowAtGrid_valid` は元の有限座標で実際の置換部分合成の行を返すことを保証する。
`horizontalRows_eq_grid`・`verticalRows_eq_grid` は範囲内の成分格子座標へ元の行列を同定する。
`fusedRows_eq_grid` は実際の全融合行列を計算可能な `fusedGridVertices` の座標評価へ同定する。
`pathSequence_rows_grid` は実際の compositionPath 上の元の置換合成列も同じ評価へ戻す。
`pathSequence_success_of_vertices` は両座標列の全体一致を入力に実際の経路表の抽出成功を与える。
`DegreePath.walkVertices_eq_blocks` は任意の始点からの交互歩行を実際の成分経路へ同定する。
`fusedGrid_eq_walk` は元の境界座標の更新と未消費次数対を使って同じ歩行を構成する。
`compositionPath_vertices_eq_grid` は実際の全経路と全融合格子列の一般の一致であり、追加仮定を残さない。
`rows_pathSequence` と `pathSequence_success` は構成した Schedule で実際の経路表の合成語抽出を証明する。
`pathSequence_eq_shuffleSimplex` は元の置換列が既存の実際の shuffle 合成単体の頂点列であることを示す。
`term_shuffleSimplex` と `signed_term_shuffleSimplex` は任意の可換環で実際の正規化項と符号付き合成項を照合する。
正の内側語長での正方向の成功表と各項の構成は完了。
`AdjacentCollapse.collapse` は連続重複だけを縮め、非退化語では元の語を保つ。
`CompositeRecovery.outerLabel`・`innerLabel` は既存の挿入ラベル直和分解で元のラベルを復元する。
`outerWord_compositeWord` は非空な分割成分の指定値の反復を縮約し、元の外側語を返す。
`inner_compositeWord` は内側射影を元の全分割成分の連結へ同定する。
`OverlapPartition.collapse_segments` は共有端点の重複を除いて元の内側語へ戻す。
`innerWord_compositeWord` は出力だけから元の内側語を復元する。
`input_words_unique` と `input_degrees_unique` は同じ合成語を与える両語・両次数の一意性。
`isInserted` の takeWhile・dropWhile は挿入語を次の外側文字で切り出す。
`splitParts_compositeWord` は元の外側語を案内に全分割成分を復元し、空部分語も扱う。
`partsOfWord_compositeWord` は出力だけから元の外側語を復元して全分割成分を取り出す。
`partition_unique` は分割長の一致から分割の一意性を示し、内側語長零も含む。
`composite_data_injective` は正の内側語長で両語・分割の依存対から合成語への単射性。
`schedule_eq_of_same_output` は元の置換列が異なる場合も成功出力の同じ Schedule を強制する。
`reduceRows_reordered_endpoint_not_isChain` は前半集合が一致する隣接行の境界重複を示す。
`reduceRows_block_endpoint_mem_middle` は中央だけを並べ替えた非退化成功二行の前行末を中央へ制限する。
`available_block_next_head_mem_middle` はその除外更新後の次行先頭も中央に属すことを示す。
`permutationComposition_vertical_endpoint_inserted` と
`permutationComposition_vertical_next_head_inserted` は実際の逆合成置換行へ適用する。
除外状態・後続 table は任意、内側 arity 零も扱う。
`available_filterMap` は部分単射の行と任意の除外状態の射影を同時に扱う。
`ExtractionPrefix.filterMap` は選択末尾を残す場合に選択語と終状態を保つ実際の抽出証跡の射影。
`innerLabel_available_composition_row` は任意の除外状態の合成可用行を元の可用内側逆置換行へ戻す。
`permutationComposition_vertical_inner_step` は非退化な成功垂直二行から元の内側一行を復元する。
`vertical_prefix_inner_projection` は垂直成分の最終行直前までの有限先行部分全体の抽出を射影する。
各行末の保持は元の成功と非退化性から導く。`vertical_prefix_inner_rows` は全行が元の内側逆置換列と一致。
`filterMap_final_prefix` は合成行が外側文字で終わっても、射影後の末尾を残す一行の抽出を構成する。
`filterMap_selection_discarded_last` はその場合に元の除外更新が内側選択語全体を除くことを示す。
`permutationComposition_vertical_inner_pair` は元の非退化成功二行から、内側末尾を残す内側二行を復元する。
`vertical_interval_inner_projection` は一歩以上の垂直成分全体を端点付きの内側抽出として復元する。
最終行の内側非空性は直前の行と非退化成功から導き、各行と選択語は実際の元の内側射影を保つ。
`CompositeRecovery.outerRemoved` は任意の合成除外から外側除外を復元し、全内側除外で指定値を除く。
`recovered_state_mem` は内外の復元状態の合成が元と同じ文字を除外することを示す。
`recovered_available_substitute` は任意の合成可用行を復元した元の二つの可用行への代入へ戻す。
`outerLabel_available_composition_row` は合成可用行の外側射影の縮約が元の可用外側行であることを示す。
内側 arity 零と全内側除外後も同じ一般定理で扱う。正の内側 arity では初期外側除外も空となる。
`AdjacentCollapse.collapse_take_prefix` と `collapse_drop_rank` は選択先頭部分と共有文字からの後続の順位を保つ。
`outerSelection_take`・`outerSelection_bounds` は縮約した実際の選択語と外側行長の正値性・上限を与える。
`outerSelection_update_mem` は元の合成除外更新と外側の末尾を残す更新の所属集合の一致。
`outerSelection_step` は復元した次状態での任意の後続成功を元の外側一行へ転送する。
`outer_table_success` は任意の成功合成表から実際の外側表の成功を構成する。
この表では垂直移動による外側置換の重複を保持する。
`rowFusion_collapse` は同じ二行の融合で成功と縮約出力が保たれることを示す。
`compressRows` は連続する同じ行を全て融合し、異なる行の順序と離れた同じ行を保持する。
`compressRows_fst` は圧縮後の行列を元の行列の連続重複縮約へ同定する。
`compressRows_success` は元の各行が非重複なら圧縮後も成功し、縮約出力が変わらないことを示す。
`compressed_outer_table_success` は合成表から圧縮外側表を作り、その縮約出力を元の外側復元語へ戻す。
`permutationComposition_horizontal_inner_boundary_eq` は同じ内側置換の両内側境界文字を一致させる。
`permutationComposition_horizontal_outer_boundary_ne` は非退化な成功の水平境界の外側値の非一致。
縮約の先頭・末尾保存と `outerSelection_nodup` を合わせ、
`horizontal_outer_selections_isChain` で水平二行の外側選択語の連結が非退化となる。
`SeparatedBoundaries` は元の抽出証跡で異なる行の境界の非一致を指定する。
`ExtractionTrace.compress_isChain` はこの条件から圧縮後の実際の出力全体を非退化にする。
`recoveredOuterTable_trace` は元の行ごとの外側復元語を実際の抽出証跡に固定する。
`recoveredOuterTable_separated` は隣接行で内側か外側の一方を固定する非退化成功から境界条件を得る。
`compressed_outer_table_nondegenerate` はその条件下で圧縮外側表の実際の出力を外側復元語そのものへ戻す。
`shuffleTableEntries_axis` は実際の ShufflePath の隣接条件を単位ステップから無条件に供給する。
`shuffle_outer_recovery` は任意の実際の成功経路表へ非退化な外側復元を適用する。
`collapse_ofFn_orderHom` は端点を保つ単位歩幅の単調写像の繰り返しを縮め、元の列へ戻す。
`shuffle_compressed_outer_rows` は経路の圧縮外側行列を元の外側行列の縮約へ同定する。
`shuffle_outer_isChain_of_success`・`shuffle_inner_isChain_of_success` は元の両置換列の非退化性を成功から導く。
`shuffle_outer_recovery_with_rows` は正の内側 arity で空の初期状態・元の外側行列と行数を持つ成功を返す。
`shuffleSimplex_outer_recovery` は既存の実際の shuffle 合成単体への直接の適用。
`output_covers` は非退化性を仮定せず、成功 Schedule の出力が全ラベルを含むことを示す。
`recurrentEnds_outerWord` は元の非最終行末の再出現を外側へ移す。
`recurrentRows_length` と `compressRows_positive_excess` は行長−1 総和を正しく固定し、圧縮で保存する。
`schedule_of_table` は成功表の元の行列と総和から実際の Schedule を構成する。
`shuffle_outer_schedule` は正の内側 arity の実際の shuffle 成功から元の外側 Schedule を復元する。
`shuffle_outer_basis` は同じ出力から元の外側次数の BasisWord と一意な成功 Schedule を返す。
`ConsumptionPrefix` は同じ行の選択長と消費長を分け、空選択・全消費・末尾保持を扱う。
`normalize` はその全区間を一つの先頭部分と厳密な終状態へ融合する。
`ExtractionPrefix.filterMap_consumption` は同じ行へ射影される抽出全体の消費証跡を作る。
`horizontal_inner_before_vertical` は実際の非退化成功から水平区間全体を元の内側一行へ戻す。
水平零歩も含み、内側の非空性・末尾保持を次の垂直移動から導いて実際の終状態を保つ。
`horizontal_inner_close` は最終射影末尾を残し、`horizontal_inner_success` は最後の水平区間を閉じる。
末尾の合成行の内側選択が空でも、区間全体が非空なら最終一行の成功を返す。
`InnerRunDecomposition` は実際の軸方向の表を水平区間に分割し、垂直辺の共通外側置換を保持する。
`sources_eq` は分割の内側置換列を元の列の連続重複縮約へ同定する。
`vertical_inner_join` は実際の成功から内側語の接続一致と次区間の内側非空性を得る。
`inner_table_success` は全水平区間を実際の終状態で接続し、全内側表の抽出成功を構成する。
`mem_innerWord`・`innerWord_covers` は復元内側語の全射性を元の出力から得る。
`shuffle_inner_recovery_with_rows` は正の内側 arity の実際の経路から元の全内側行列・行数を復元する。
復元語は元の出力の内側復元そのもので、非退化性・全射性も証明済み。
`ExtractionPrefix.recurrent_tail` は元の全行末の再出現を実際の先行抽出の後へ渡す。
`InnerRunDecomposition.inner_recurrent` は垂直直前の保持末尾から全内側復元の行末再出現を得る。
`shuffle_inner_schedule` は余剰総和 n−1 と元の行数から、元の内側次数の成功 Schedule を構成する。
`shuffle_inner_basis` は合成出力だけの内側復元語から元の次数の BasisWord と一意な成功 Schedule を返す。
正の内側 arity では実際の shuffle 成功から元の両入力語・次数・一意な成功 Schedule を復元済み。
`collapse_append_length` は非退化な二語の連結で失う境界の一コピーを正確に数える。
`shared_endpoints_of_saturated` は非空非退化な全部分語の長さ飽和から全共有端点を強制する。
`shared_rows_take` は各部分語を累積部分長−1 から切った全縮約語の区間へ戻す。
`OverlapPartition.ofRows` は部分語長から既存の有限分割添字を構成する。
`ofRows_segments`・`existsUnique_of_rows` は指定した内側語で全部分語を持つ分割の一意な存在を証明。
共有端点は追加仮定にせず長さから導き、離れた同値を含む部分語も扱う。
`exists_nonempty_parts` は任意の非退化出力を復元外側語への非空部分語の代入に分解する。
`splitParts_properties` は実際の計算結果の非空性・内部非退化性・個数と全代入一致を証明する。
部分語分解は内側 arity 零も含む。
`recovered_partition_existsUnique` は両復元語の本来の次数と出力長から一意な分割と合成語一致を得る。
`shuffle_source_partition` は正の内側 arity の実際の成功から元の両基底語・一意な分割・
合成語一致・元の両置換列での一意な成功 Schedule を全て返す。
`selected_eq_of_same_output` は左右で異なる置換列の成功出力から全選択行列を一致させる。
`boundaryInserted_iff_notMem` は実際の選択行列の内側二端の境界と垂直辺の同値を証明する。
`shufflePath_eq_of_same_output` は同じ非退化出力を持つ二つの成功経路を一致させる。
`TableCompositionData.compositionPath_eq_of_success`・`fusedSchedule_eq_of_success` は
正方向で構成した経路と Schedule を元の実際の成功へ戻す。
`TableCompositionData.eq_of_same_output` は同じ元の置換列・挿入位置・合成出力の入力データ一意性。
`shuffle_reconstruction_existsUnique` は正の内側 arity の実際の非退化成功から、
元の両成功表・両語・分割を持ち、経路・Schedule・出力を全て戻すデータを一意に構成する。
`CompositionSuccess.Source` は元の両置換列と挿入位置を固定した全成功二表・分割。
`Target` は実際の非退化成功を持つ全経路・Schedule の有限な部分型。
`CompositionSuccess.equiv` は正の内側 arity で両者の全単射を構成する。
`sourceFintype` はこの全単射で元データの有限型構造を構成し、和の中だけで局所的に選ぶ。
`forward_term` は各項の値と既存の経路符号を保つ。
`sum_all_eq_source` は失敗・退化出力項を零として全経路・全 Schedule の和へ戻す。
`sum_onSequence_eq_source` は全 shuffle 符号付き onSequence の和を元の全成功二表・分割の和へ同定する。
`SuccessfulWord` と `onSequence_eq_sum_successfulWords` は各元列の TR を成功基底語の有限和へ展開する。
`wordsEquiv` は元データを二列の成功基底語と分割の依存直和へ移す。
`sum_source_eq_partialComposition` は元の側の全有限和を二つの onSequence の部分合成へ同定する。
`onSequence_partialComposition_of_pos` は任意の可換環・全次数・正の内側 arity の全 shuffle 和の合成保存。
`normalizedMap_shuffleBilinear_of_pos` は正規化生成元の一致を全正規化鎖の双線形合成へ延長する。
正の内側 arity の実際の TR の部分合成保存は完了。
`normalizedMap_shuffleBilinear_nullary_succ` は零 arity・正の内側次数の合成保存。
各実際の shuffle の垂直辺で隣接頂点が一致するため、TR は零となる。
`eraseSlotWord` は指定値の削除とラベルの詰め直し。空語代入と実際の BE 逆置換行に一致する。
`compositionOnWords_nullary_of_count_eq_one` は一出現の空語合成を削除語の正規化へ同定する。
`permutationComposition_nullary_available` は元の除外状態と実際の合成行の可用語を比較する。
`reduceRows_eraseSlotWord_of_mem` は指定値を早期除外した全抽出と削除の可換性。
`reduceRows_nullary` は実際の全合成表を元の早期除外表へ同定する。
`nullary_success_extension` は解放値探索により一行を延長し、指定値を一回だけ挿入した成功表を構成。
`nullary_success_schedule` は延長表を元の次数の Schedule に包装する。
`isChain_insert_of_eraseSlotWord` は削除後の非退化性を元の語へ戻す。
`nullary_successfulWord_lift_exists`・`lift_term` は実際の目標成功基底語から元の一出現成功項を構成し、項の値を保つ。
`FilterMapReady` は全選択の非空性と非最終行末の保持条件。
`recurrentEnds_eraseSlotWord_ready` は高々一出現と行末の再出現からこの条件を導く。
`nullary_forward_schedule` は一出現の元の成功表から実際の nullary 成功 Schedule を構成する。
`NullarySource` は一出現で削除後も非退化な元の有限成功項。
`nullaryForward` は実際の目標成功項への全射で、`nullaryForward_term` は空語合成の項の値を保つ。
`nullary_success_output_unique` は同じ削除出力を持つ一出現の元の成功出力の一意性。
`nullarySuccessEquiv` は元の非零候補と実際の目標成功項の有限全単射。
`sum_nullary_all_eq_source` は複数出現・退化の零項を含む全成功基底語の和へ戻す。
`onSequence_partialComposition_nullary_zero` は出力 arity 零を含む空語の全 shuffle 和の合成保存。
`onSequence_partialComposition` は任意の可換環・全 arity・全次数の一般公式。
`normalizedMap_shuffleBilinear` は実際の全正規化鎖に対する双線形 shuffle 合成保存。
nullary を含む TR の部分合成保存は完了。
`Surjection.partialComposition_d_positive`・`d_leftZero`・`d_rightZero` は χ の Leibniz 則の全分岐。
`unitElement` と左右の単位則、内外右作用の同変性、入れ子と Koszul 符号付き並列結合則も全射 TR から証明。
`Surjection.complex` は実際の非有界整数コチェイン複体。`complexXIso` は負次数と全射語加群の比較。
`complexRename` と `Surjection.sequence` は値の左置換を持つ複体の対称列。
`TableReduction.cochainMap` は実際の整数複体の TR、全非正次数で全射。
`TableReduction.sequenceMap` は整数複体の対称列の TR 自然変換。
`Surjection.cochainCompositionBilinear` は全整数次数の双線形部分合成。
`cochainMap_compositionBilinear` は整数 TR の合成保存、`cochainMap_f_surjective_int` は全整数次数の全射性。
`Surjection.complexPartialComposition` は全整数 Leibniz 則を `tensorLift` で束ねた実際の部分合成射。
`complexPartialComposition_neg_tmul` は元の全射語の合成による負次数の評価。
`TableReduction.complexPartialComposition_comm` は整数複体の射としての TR の部分合成保存。
`Surjection.complexUnit` は BE の単位と TR の合成で、零次数では一文字単位と一致する。
複体射の左右単位則と内外同変性も TR の全射テンソルで消去して証明済み。
`tensor_epi_of_epi` は整数加群複体の全射のテンソルの全射性。平坦性・cofibrancy は仮定しない。
χ の複体射の入れ子・並列結合則も三重テンソル TR で消去して証明済み。
`Surjection.operad` は実際の全射語 dg オペラッド、`TableReduction.operadMap` は一般の TR : E → χ。
全 arity・全整数次数・任意の可換環を扱い、nullary の合成保存も含む。
`IntervalCuts.edgeValue`・`vertexValue` は Δ¹ の切断公式の符号付き基底値。
`edgeLinear`・`vertexLinear` は全射語加群への線形延長。
辺の非零項は d+1≤n、頂点の非零項は d=0。辺の出力の次数和も d+1 と証明済み。
符号は BF §2.2.4 の区間長による交換指数と内側区間の右端点の指数を使う。
010 の辺⊗辺の正符号、101 の負符号、通常の AW の辺⊗一・零⊗辺を監査で検証。
`IntervalCuts.interval` は既存の正規化関手による実際の N_*(Δ¹) の整数表示。
各面を正規化生成元へ送り、`tensorVector` で右括弧の反復テンソルの斉次元へ接続。
`edgeComponent`・`vertexComponent` は全射語加群から実際の区間テンソル成分への線形写像。
`edgeChain_d`・`faceVector_edge_d` は辺の微分＝終点−始点を自然数鎖・整数表示で証明する。
`intervalChains_isZero` は鎖次数 >1 の零性、`interval_isZero_positive` は整数正次数の零性。
`tensorVector_d` は反復テンソルの境界を因子ごとの Koszul 符号付き有限和へ展開する。
`tensorBoundaryTerm_eq_zero_of_vertex` で頂点因子を消し、`tensorVector_d_eq_sum_edges` で辺だけへ制限。
`tensorBoundaryTerm_zero_edge` は先頭辺の境界を二端点のテンソルの差として明示する。
頂点だけの任意の出力族が閉じることも証明済み。
`edgeNondegenerate_iff` は非零切断を左右の語の単射性で特徴付ける。
同じ色の反復は切断点を跨ぎ、`edgePositionExponent_eq_zero` で非零切断の位置指数は零。
活動位置（区切りと切断点）は d+1 個で、互いに異なる色の出力辺と対応する。
`edgeOutput_tensorVector_d` は実際の境界を元の活動位置の和へ添字替えする。
`eraseCutBasisWord` は切断点以外の反復文字の削除後の実際の非退化基底語。
`edgeOutput_eraseCut_left`・`right` は削除後の全出力族を、その色の終点・始点への置換と同定する。
`edgeSign_eq_inversionCount` は非零切断の符号を活動位置の色の逆転数へ同定する。
`positionInversionSign_erase` は一位置削除で元位置順位と色順位の符号が交換する公式。
`activePositions_erase_image_eq_erase` は削除後の活動集合を元の一位置削除へ同定する。
`edgeSign_erase_left_boundary`・`right_boundary` は切断点を残す左右削除で実際のスカラー係数を一致させる。
`tensorBoundaryTerm_eq_endpoints` は任意の辺因子の境界を前方次数符号付きの二端点置換の差で表す。
`endpointTensor` は置換後の出力族の実際のテンソルで、`endpointTensor_eraseCut_left`・`right` は
それを左右の実際の削除語の切断出力へ同定する。
`cut_factor_boundary` は切断符号付きの反復色一因子の境界を、両削除係数で重み付けした和へ同定する。
`original_cut_iff_no_same_side_repeat` は削除後だけ非零となる原因を削除文字の同側重複へ限定する。
`CutDeletionDefect` はその障害位置で、存在と一意性を証明済み。
障害が切断点以外なら削除位置と障害位置を交換でき、`NonpivotResidualCut.swap` は
同じ元切断点を保つ有限型上の固定点なし対合。`swapEquiv` はその自己同値。
`residualCut_output_family`・`residualCut_tensor_eq` は交換対の実際の削除基底語の出力族・テンソル値の一致。
`NonpivotResidualCut.swap_coefficient` は同色三出現も含む一般の削除・切断係数の反対性。
`residualCut_tensor_sum_eq_zero` は全非切断点障害項の実際のテンソル値の有限和が零であること。
`edgeNondegenerate_between` は非零切断集合の凸性、`edgeSign_pivot_boundary` は切断点色の共通係数。
`gapOutput`・`gapTensor` は語の隙間で二分した出力族・実際のテンソル値。
`pivotBoundary_gap_difference` は実際の切断点色の因子境界を共通係数付き隙間差へ移す。
`pivotBoundaryValue_sum` は全有限和を非零切断区間の両端へ集約し、非零切断がなければ零とする。
`pivotBoundaryValue_sum_zeroDegree` は arity 零を含め、次数零の全和を入力辺の二端点差へ同定する。
`GapNondegenerate` は隙間の左右単射性。隣接退化辺切断の反対側の同色位置は一意。
`erase_pivot_iff_gap_before`・`after` は切断点同色削除後の非零性と隙間の非退化性の同値。
`pivotEraseBasisWord` は実際の削除基底語、`pivotErase_tensor_before`・`after` はその値と隙間値の一致。
監査の `01202` は元の非零切断がないが、左右の異なる削除項が同じ隙間へ戻る例。
`pivotDeletion_coefficient_before`・`after` は左・右削除係数を共通係数の負・正へ同定する。
`pivotDeletion_weighted_pair` は同じ隙間へ戻る二つの実際の符号付き削除テンソルの相殺。
区切り色の逆転数が奇数の `20121` でも一般係数公式を監査済み。
`PivotResidualCut` は切断点障害の有限添字、`beforeEquiv`・`afterEquiv` は隙間の隣接退化切断との有限同値。
`pivotResidualValue_sum` は実際の全削除和の隙間への添字替え。
`pivotResidualValue_sum_eq_boundary` は正次数の全切断点障害削除和と全切断点色因子境界和の一致。
元の非零切断がない `01202` と、二つある `01203` の全削除和も監査済み。
`NormalizedDeletedCut` は全射な削除語と非零切断の共通有限添字、`word` は実際の削除基底語。
`NormalizedDeletedCut.sum_three` は元切断非零・非切断点障害・切断点障害の三部分分割。
`normalizedDeletedValue_sum_reduce` は二障害部分を処理し、元切断非零部分と切断点色全境界和へ帰着する。
元の非零切断がなければ `normalizedDeletedValue_sum_eq_zero_of_no_cut` により正規化全削除和も零。
`NormalizedDeletedCut.fiberEquiv` は削除位置ごとの非零切断和と共通有限添字を結ぶ。
`edgeComponent_generator` は任意の語の生成元の実際の辺成分を非全射・退化も含めて展開する。
`edgeComponent_differentialOnWord` は実際の削除微分の辺成分と正規化全削除和の一致。
`edgeComponent_differentialOnWord_reduce` は元切断非零部分と切断点色全境界和へ帰着する。
元の非零切断がなければ、実際の削除微分の辺成分も零となる。
`regularCutEquiv` は元切断非零削除項と反復位置対・左右側の有限同値。
`RepeatCutPair.factorBoundary_eq_pair` は共通次数での一反復色境界と実際の二削除値の一致。
`edgeComponentOnWord_boundary_factors` は実際の辺成分の微分を全反復色・切断点色境界へ分ける。
`edgeComponentOnWord_d_positive` は正次数の実際の辺成分と削除微分の可換性。
`edgeComponentOnWord_d_zero` は次数零の辺成分の微分と入力辺の二端点差の一致。arity 零も含む。
`degreeOne_deletion_pair` は次数一の唯一の反復色の削除係数 +1・−1 と他係数零。
`vertexComponent_differentialOnWord` は実際の頂点成分に送った全削除微分の零性。
`vertexComponentOnWord_d_positive`・`d_eq_zero` は頂点入力の微分保存と出力の閉性。
`ComponentLinearIdentities` は頂点・辺の全微分条件を全射語加群全体の線形等式として公開する。
`vertexChainLift`・`edgeChainLift` は任意の二頂点値・一辺値を実際の正規化区間へ線形延長する。
`rawEdgeLift_degeneracies_zero` が実際の退化消滅を供給し、生成元での評価も証明済み。
`vertexInputBilinear`・`edgeInputBilinear` は全射語加群と実際の整数区間成分の双線形余演算。
頂点・辺生成元では既存の `vertexComponent`・`edgeComponent` の値と一致する。
`vertexInput_hom_ext`・`edgeInput_hom_ext` は実際の区間上の射を二頂点・一辺で比較する外延性。
`InputLinearIdentities` は区間の任意の入力に対する微分の線形等式を与える。
`cochainActionBilinear_d` は零成分を含む全整数次数の Koszul Leibniz 則。
`cochainAction` は実際の複体射 `χ(n) ⊗ interval → interval^{⊗n}` であり、
`cochainAction_neg_vertex`・`neg_edge` はその値を構成済みの有限切断へ戻す。
`cochainAction_unit` は χ の一文字単位の作用と単位子の一致を全整数複体の射として証明する。
`edgeOutput_rename` は色を置換した全出力族の逆置換公式。
`edgeNondegenerate_rename_iff`・`activePositions_rename` は非零性と活動位置を保存する。
`swapFirstIso_apply` は実際の複体の先頭二因子交換の Koszul 符号を評価する。
`adjacentIso_tensorVectorAt` は任意位置の実際の面テンソルの隣接交換公式。
`edgeSign_adjacent` はその二出力次数の積と切断符号の変化が一致すること。
`edgeComponentOnWord_permutation`・`vertexComponentOnWord_permutation` は全語基底の任意置換の公式で、
`ComponentPermutation`・`InputPermutation` は全語加群と区間の任意の入力へ線形に延長する。
`cochainAction_equivariance` は全 arity・全整数次数の複体射としての対称群等変性。
`CompositionSlotGeometry` は非零外側切断の指定色の一・二出現と辺・頂点出力の分類。
`OverlapPartition.twoEquiv` は正長語の二部分割と共有位置の有限同値。
`NestedEdgeCut` は内側辺切断または零語次数の頂点入力からなる有限添字で、`partition` は合成分割を構成する。
`edgeComponent_composition_cut_sum` は合成係数の実際の辺成分を分割・合成語切断の二重和へ展開する。
`cochainAction_partialComposition_edge_tmul` は実際の複体射の左辺を自然数次数の双線形成分へ戻す。
`compositeOuterPosition` は指定色以外の外側位置の実際の合成位置で、値も元の残りラベルと一致する。
`compositeInnerPosition` は一出現挿入の内側位置で、挿入ラベルの値を実際の合成語で評価する。
`edgeNondegenerate_iff_list_nodup` は辺切断の非退化性を左右の take・drop の重複消滅へ直す。
`splice_cut_nodup` と `SingleSlotLists` は非交差な前後の代入像を内側の切断へ連結する。
`composite_single_slot_cut_nondegenerate` は切断点色への一出現挿入の合成切断の非退化性。
`NestedEdgeCut.compositePosition` は二段切断の全分岐で実際の合成位置を返し、切断点の文字も比較済み。
`compositePosition_pivot_nondegenerate` はその切断点色分岐の非退化性を供給する。
`substitute_nodup_of_parts` は外側と各挿入部分語が Nodup なら代入後も Nodup であること。
`composite_non_slot_cut_nondegenerate` は同じ条件で非切断点色の切断を保つ。
`partition_segments_nodup_of_nonpivot` は二段切断で選んだ一・二部分割がその条件を満たすこと。
`NestedEdgeCut.toCompositeCut` は全分岐で実際の非零合成切断へ送る写像で、`toCompositeCut_injective` が単射性。
`remaining_count_substitute` は零 arity を含む残り色の出現数保存で、`exists_unique_outer_pivot` が残り色の切断位置を戻す。
`outer_cut_nondegenerate_of_slot_counts` は外側の非零性の復元を指定色の左右一出現条件へ帰着する。
`composite_single_slot_cut_nondegenerate_iff` は一出現挿入の内側位置で外側・内側の非零性を復元する。
`exists_single_slot_cuts_of_inserted_pivot` は一出現性の下で挿入ラベル切断点から両非零切断を戻す。
`compositeSegmentPosition` は全挿入部分語の実際の位置を構成し、異なる部分語の順序も保存する。
`compositeSegment_boundary_straddles` は隣接部分語の共有端点の二出現が非零切断点を厳密に跨ぐこと。
`slot_occurrenceCount_le_two_of_composite_cut` は外側指定色の出現数を高々二へ制限する。
`slot_occurrenceCount_eq_one_of_inserted_pivot` は挿入ラベル切断点の場合に一出現性を導出する。
`exists_preimage_of_inserted_pivot` はその合成切断が二段切断からの写像の像に入ることを示す。
`outer_cut_nondegenerate_of_compositeOuterPosition` は残りラベル切断点の外側非零性を復元する。
`segment_nodup_of_same_side` は片側の部分語の Nodup を戻し、一部分割の内側次数零と二部分割の非零切断を供給する。
`NestedEdgeCut.toCompositeCut_surjective` は両分岐の全射性で、`compositeCutEquiv` は正 arity の有限同値。
`edgeComponent_composition_nested_cut_sum` は実際の合成辺成分をこの有限同値で二段切断上の和へ移す。
`OutputListMembership` と `InsertedMembership` は出力頂点を左右のリストと消費済み部分語への所属で特徴付ける。
`NestedEdgeCut.compositePosition_remaining_output` は全残り色、`compositePosition_inserted_output` は全挿入色の公式。
`NestedEdgeCut.outputFamily` は二段作用の全出力族で、`compositePosition_outputFamily` が実際の合成切断の族と照合する。
`edgeComponent_composition_nested_output_sum` は共通全次数で同じ出力族の実際の面テンソル和へ移した左辺。
`lineRank_after_pivot_eq_degree` は非零切断点以後の行番号が語次数であること。
`segmentDegree_two_zero/one` は非零内側切断の二部分語の行次数がそれぞれ内側全次数・零であること。
`NestedEdgeCut.compositionSign_pivot/vertex` は合成符号が正、`compositionSign_nonpivot` は最初の出現の後続次数による公式。
`appendIso_tensorVectorAt`・`appendIso_inv_tensorVectorAt` は実際の面テンソルの連結・分割を全指定整数次数で評価する。
`tensorCoInsertionAction_on_blocks` は既存の指定位置の余代入を同じ前後ブロックへ接続する。
`coInsertionBlocks_apply`・`coInsertionBlocks_face_apply` は係数次数×前方次数の交換符号と実際の面テンソル値を評価する。
`insertionFamily_eq_blocks`・`family_eq_blocks` は置換族・元の族の前方・指定因子・後方表示。
`tupleDegree_prefixFamily` はブロックの次数と既存の prefixDegree の一致。
`NestedEdgeCut.outputFamily_eq_blocks`・`innerOutputFamily_tupleDegree` は二段出力族と内側次数をこの表示へ接続する。
`tensorVectorAt_family_blocks` は元の面テンソルを実際のブロック評価の入力へ分ける。
`tensorCoInsertionAction_face_apply` は内側の指定面テンソル値から元の族上の実際の余代入と prefixDegree の交換符号を評価する。
`FaceCut` は辺・頂点入力の非零項を統一し、正次数の頂点入力は空、次数零は一項となる。
`cochainAction_basis_face_cut_sum` は全入力面での実際の複体射の値をその有限和へ移す。
`tensorCoInsertionAction_cochain_basis_sum` は全 arity の実際の内側作用の余代入を評価する。
`NestedEdgeCut.faceCutEquiv`・`sum_faceCuts` は外側切断上の内側面切断和を二段切断上へ移す。
`iteratedCochainAction` は係数交換・外側作用・内側余代入を含む実際の全右辺。
`iteratedCochainAction_basis_edge_nested_sum` はその辺入力を同じ二段切断と全出力族の和に移す。
`NestedEdgeCut.actionCoefficient` は二交換の符号を `(-1)^(d*e + e*prefixDegree)` にまとめた整数係数。
`outputFamily_tupleDegree_all` は内側 arity 零も含む全出力次数の公式。
`cochainAction_composition_basis_edge` は実際の左辺を既存の合成語加群の辺成分へ戻す。
`remainingPositionMap_image_of_degree_zero` は非辺への次数零代入が全活動位置を順序を保って移すこと。
`NestedEdgeCut.compositionCoefficient_vertex` は内側が頂点へ作用する全分岐で一般係数が一致すること。
`compositionEdgeCutTerm_vertex` はその分岐の実際の合成切断項と二段作用の面テンソル項を同定する。
`activePositions_pivot_union` は切断点色への挿入の全活動集合を、外側切断点を除いた像と内側活動像へ分ける。
`inversionCount_pivot` は内部二項と内側活動数倍の交差逆転数の公式。
`compositionCoefficient_pivot`・`compositionEdgeCutTerm_pivot` は同分岐の一般係数と実際の項の一致。
`activePositions_nonpivot_union` は二出現色の最初の活動位置を内側活動列で置き換える全活動集合の公式。
`inversionCount_nonpivot` は前後両向きの交差逆転の公式で、`compositionCoefficient_nonpivot` が同分岐を閉じる。
`NestedEdgeCut.compositionCoefficient` は全三分岐の一般係数一致。
`edgeComponent_composition_action_sum` は実際の合成辺成分を二段作用と同じ係数の有限和へ移す。
`cochainAction_composition_basis_edge_eq_iterated` は正の内側 arity・全語次数の語基底と辺で実際の左右の作用が一致すること。
`vertexComponent_composition_zero` は次数零の唯一分割による合成頂点値。
`iteratedCochainAction_basis_vertex_outer_positive/inner_positive/zero` は元の頂点での全 arity の二段作用の値。
`cochainAction_composition_basis_vertex_eq_iterated` は正の内側 arity・全語次数の語基底と両頂点で実際の左右の作用が一致すること。
`coefficient_interval_hom_ext` は全整数三重斉次成分を語基底と区間の三生成元へ帰着する。
`cochainAction_comp_positive` は正の内側 arity の部分合成則を全整数複体射として証明する。
`cochainAction_operad_comp_positive` は実際の χ オペラッドの comp と二段作用の四射での表示。
`vertexComponent_composition_zero_all` と `cochainAction_composition_basis_vertex_eq_iterated_all` は nullary を含む両頂点の合成則。
`NestedEdgeCut.nullary_occurrenceCount` は空語の非零二段切断の指定色が一出現であること。
`cochainAction_composition_basis_edge_nullary_eq_iterated_of_count_ne_one` はそれ以外の実際の左右の零性。
`nullaryRawWord` は退化し得る削除語を保持し、`nullaryRawWord_cut_iff`・`nullaryNestedCutEquiv` が全非零切断を対応させる。
`nullaryNestedCutEquiv_outputFamily` と `NestedEdgeCut.nullary_edgeSign` は全出力族・活動位置の逆転数・切断符号の保存。
`edgeComponent_composition_nullary_action_sum` は実際の左辺を右辺と同じ整数係数の和へ移す。
`cochainAction_composition_basis_edge_nullary_eq_iterated` は空語の辺入力の全外側語次数の合成則。
`cochainAction_comp` は nullary・出力 arity 零を含む全整数複体射の部分合成則。
`surjectionCoalgebra` は実際の区間切断作用の χ-coalgebra、`barrattEcclesCoalgebra` は一般 TR に沿う E への制限。
`endpoint` は元の両頂点からの単位複体の射、`contraction` は実際の AW 余単位。
`endpoint_contraction` は双方で恒等となる三角形。
`contractionHomotopy` は一頂点を辺へ送る具体的な次数 −1 の鎖ホモトピー。
`contractionHomotopyEquiv`・`contraction_quasiIso`・`endpoint_quasiIso` は収縮の鎖ホモトピー同値と、収縮・両端点の擬同型性。
`intervalMap` は閉じた両頂点と、その差を境界に持つ辺から任意の非有界複体への射を構成する。
`interval_hom_ext` は全整数複体射の三生成元外延性。
`interval_relative_lift` は全射な擬同型に沿い両端点を固定して区間射を持ち上げる。
`boundary_cofibration` は実際の二端点包含が生成類に対する左持ち上げ性を持つこと。
`Surjection.zeroAugmentation` は零次の全語基底を一へ送り、TR と BE augmentation の零次を比較する。
`zeroTensor` と正次数の頂点値零性から、端点・収縮の全 arity の余作用保存を証明。
`endpoint_coaction`・`contraction_coaction` は実際の全整数複体射の等式。
`coalgebraInterval` は元の両頂点・AW 収縮・境界 cofibration を含む具体区間。
`BarrattEccles.modelCategory` は AW Hopf 構造とこの区間を完全な抽象転送へ代入する。
弱同値は底の擬同型、fibration は全次数全射で、自由像の生成類で生成される。
`BarrattEccles.forget_isRightQuillen` により E2a-4 の右 Quillen 性も完了。
`BarrattEccles.isFibrant` は局所モデル構造ですべての E 代数の fibrancy を与える。
`fibration_iff`・`weakEquivalence_iff` で底の全射性・擬同型を直接使える。
`pullbackFunctor_isRightQuillen` は slice で底を固定した引き戻しの二つの右類の保存を示す。
`pullbackFunctor_hasPointwiseRightDerivedFunctor` により、その右導来関手が存在する。
`fibrationReplacement` は任意の左脚の実際の分解で、包含は擬同型、射影は全次数全射。
`homotopyPullback` はその射影と元の右脚との引き戻し。
`homotopyPullbackDerivedIso` はこれが右導来引き戻しの値であることを任意の局所化で証明する。
`homotopyPullbackCarrierIso` は忘却後を同じ置換の複体の引き戻しに同定する。
`homotopyPullbackCarrierDerivedIso` は底でも実際に右導来引き戻しを計算することを保証する。
`Operad.restrictAlgebra` は任意のオペラッド射に沿い、底の複体と射を保って代数を制限する。
`powerProduct` は空積を含む反復積で、連結・任意位置への代入・射の保存を証明済み。
`powerProduct_permutation` は可換モノイド対象で全置換の不変性を与える。
`commutativeAlgebraFunctor` は実際の可換モノイド複体から全 arity の Com 代数を作る。
`discreteCommutativeFunctor` は既存の対称モノイダル零次埋め込みを用い、通常の積と単位を移す。
`BarrattEccles.discreteAlgebraFunctor` は実際の augmentation E → Com に沿ってこれを制限する。
底は元の加群の零次複体、射も元の代数射の零次埋め込みである。
`HomologyZero.classMap` は閉零次元から元の `homology 0` への全射で、零類と境界の同値を証明。
`unitClass_eq_iff` は単位からの射の類の一致と鎖ホモトピーを同定する。
`unitHomLinearEquiv` は実際の H⁰ と単位からの鎖ホモトピー類の線形同値。
`HomologyZero.pairing` は任意の二入力複体射から実際の H⁰ の双線形作用を作り、
代表元独立性・ホモトピー不変性・Koszul 交換との両立まで証明する。
`BarrattEccles.homologyProduct` と `homologyOne` は E の arity 2・0 から積と単位を作る。
`homologyProduct_eq_pairing` は augmentation が一である任意の係数で同じ積を計算できること。
`homologyBinary_discrete`・`homologyNullary_discrete` は離散 E 代数の射が元の積・単位に厳密に一致すること。
`homologyCompositionHomotopy` は零入力を含む全位置の部分合成と選んだ演算を鎖ホモトピーで比較する。
`homologyProduct_assoc`・`homologyProduct_one_left/right`・`homologyProduct_comm` は実際の H⁰ の環公理。
`homologyCommRing` は元の加法を保つ可換環、`homologyAlgebra` は元の A 加群作用と両立する代数構造。
`homologyCommAlgebra` は実際の H⁰ を可換 A 代数として束ねる。環・代数構造は局所的に選ぶ。
`Operad.AlgebraDiagram` は任意の小圏の各頂点の自由図式と評価の随伴、生成射の小対象性を与える。
`BarrattEccles.Diagram.projectiveModelCategory` は自由生成セルの非循環性から完全な図式モデルを作る。
図式の弱同値は各頂点の擬同型、fibration は各頂点・全整数次数の全射。すべての図式が fibrant。
`Diagram.localizedForget` は同じ複体図式の局所化への右導来忘却で、元の忘却との自然同型を持つ。
`productFunctor_isRightQuillen` と `productDerivedIso` は空積を含む小積が右導来積を計算すること。
`product_map_weakEquivalence` は任意の小積のホモトピー不変性、`productCarrierIso` は底の積との同型。
`rightFrameFamily` は具体モデルの関手的分解から、すべての E 代数に関手的な右 frame を作る。
`cotensor` は任意の単体集合に対する実際の余テンソルで、`cotensorHomEquiv` が射の普遍性を与える。
単射に沿う制限は fibration、anodyne 射に沿う制限は自明 fibration となる。
`cotensorCarrierIso` は同じ frame の底の複体による計算との同型で、単体集合の射にも自然。
`weightedCotensor` は任意の小図式と任意の単体的重みの右 frame の end を E 代数として構成する。
`weightedCotensorHomEquiv` は全単体の実際の重み付き錐の普遍性。
`weightedCotensorCarrierIso` は同じ図式・重み・frame を用いた底の複体の end との同型。
これらに単体集合の完全なモデル構造は使わず、未証明項目を含む既存 Kan–Quillen 入力も import しない。
`HomotopyWeight.weight` は自由境界の小対象分解による実際の射影 cofibrant な一点重み。
`HomotopyWeight.coneSpace_map_boundary_rlp` と `coneSpace_map_fibration` は、
射影 cofibrant 重みの錐空間が頂点ごとの境界の右類と Kan fibration を保つことを与える。
`coneSpace_kanComplex` は Kan 値図式の錐空間の Kan 性、
`coneSpace_map_isIso_of_boundary_rlp` は anodyne 反転後の同型を与える。
これらに単体集合の完全なモデル構造の仮定はない。
`comparison_rlp` は各値の境界右持ち上げ性で、各値の Kan 性・切断・実際の収縮も構成済み。
切断と収縮は各頂点ごとのもので、添字圏に自然な切断は主張しない。
`weightedCotensor_map_fibration` は重みの射影 cofibration に沿う制限が fibration となること。
`framedLimitFunctor` はこの重みで計算する実際の小図式上の関手、`framedLimitCarrierIso` は同じ底の計算との同型。
`coneToFramedLimit` は通常の錐からの射で、固定した図式の錐の射に自然。
`limitComparisonNatTrans` は通常の極限から計算関手への実際の自然変換。
`framedLimitConeSpace` は同じ重みと右 frame への錐空間で、試験始域を具体的に cofibrant 置換する。
`framedLimitConeSpace_kanComplex` はその Kan 性、`framedLimitConeSpace_map_isIso` は
頂点ごとの擬同型の anodyne 反転後の同型性。図式モデルや元の代数の cofibrancy は要求しない。
`FrameHom.map_isIso_of_pointwise_cofibrant` の自然な Brown 分解と、
`HomotopyWeight.frameCone_source_weakEquivalence_isIso` がこの比較を与える。
`HomotopyWeight.tensorFrame` は同じ重みに標準単体をテンソルして実現する Reedy cofibrant frame。
単体作用素は弱同値で、`tensorFrameHomIso` はその実際の Hom と元の重み付き錐の自然同型。
`frameConePiZeroLocalizationEquiv` は錐の π₀ と元の実現対象からの局所化 Hom の同値。
零単体の計算と係数 frame の射に関する自然性も証明済み。
`realization_map_frame_weakEquivalence` はこの比較で係数の弱同値を検出する。
`framedLimitFunctor_map_quasiIso` は具体的な計算関手の頂点ごとの擬同型保存。
`constantDiagramReplacement` は同じ始域 frame と射影一点重みから作る、定値図式の関手的な置換。
`constantDiagramComparison` は元の代数の射に自然で、各値で擬同型。
置換は実際の射影図式モデルで cofibrant、元の代数には cofibrancy を仮定しない。
`constantDiagramHomEquiv` は置換からの図式射と始域 frame の重み付き錐の同値。
`constantDiagramLocalizedIso` は定値図式との局所化後の自然同型を与える。
`constantDiagramFrameFamily` は同じ置換を全次元の図式 frame へ拡張する。
frame は射影図式モデルで Reedy cofibrant、単体作用素と元の定値図式への augmentation は弱同値。
augmentation は元の代数の射にも自然。Reedy 自明 fibration であることは要求しない。
`constantDiagramFrameHomIso` は実際の frame Hom と Kan な `constantDiagramSourceHom` の同型。
`constantDiagramSourcePiZeroEquiv` はその π₀ と元の定値図式からの局所化 Hom の同値で、終域の射に自然。
`constantDiagramSourceClass` の像は元の同じ図式射の局所化となる。
`Diagram.mappingSpace` は実際の図式モデルから作る Kan な Map^h、π₀ は元の図式の局所化 Hom。
`constantDiagramFrameMappingComparisonIso` は選んだ Map^h と具体的な frame Hom の両変数での自然比較。
`constantDiagramSourceMappingComparisonIso` はそれを重み付き錐へ移す。
比較は任意の anodyne を反転する関手の後で成立し、単体集合のモデル構造は使わない。
`FrameHom.MixedFrame.mixedConeComparisonIso` は、任意の射影 cofibrant 重みについて
始域 frame の錐と右 frame の錐を anodyne 反転後に比較する一般界面。
共通の混合 Hom の対角が Kan であるとは仮定せず、実際の関手的 Kan 置換を介する。
`HomotopyWeight.coneSpace_map_isIso_of_pointwiseKan` は Kan 値図式の各値の局所化同値を
重み付き錐で反転し、単体集合やその図式圏の完全なモデル構造を使わない。
`kanConeComparisonIso_fac` は同じ元の比較射の像の一致、
`kanConeComparisonIso_naturality` は元の可換四角形に関する自然性を与える。
`rightSimplicialFrameFamily` は既存の右 frame の同じ単体図式表示で、元の代数に自然。
`rightSimplicialConeComparisonIso` は二重反対圏の添字を照合する錐関手の自然同型。
`framedLimitProbeComparison` は既存の試験始域から元の代数への擬同型で、
`framedLimitProbe_cofibrant` は混合 Hom の入力条件を追加仮定なしで供給する。
`sourceRightConeComparisonNatIso` はこの試験始域の始域錐と既存の右錐との終域自然な比較。
`framedLimitConePiZeroEquiv` は右錐の π₀ を元の定値図式からの局所化 Hom と同定し、
`framedLimitHomPiZeroEquiv` は同じ π₀ を元の計算対象への局所化 Hom と同定する。
`framedLimitDerivedHomEquiv` はこの二つを合成した、元の対象ごとの導来 Hom の同値。
`framedLimitDerivedHomEquiv_target` は元の図式射による後合成との両立を与える。
`framedLimitProbeFunctor` と比較自然変換は既存の同じ試験始域を関手へ束ねる。
`framedLimitConeBifunctor` と `constantDiagramSourceBifunctor` は元の二つの錐を
始域に反変・終域図式に共変な関手として保持する。
`sourceRightConeComparisonIso_source` は同じ具体的な両錐比較の始域自然性。
`constantDiagramSourcePiZeroEquiv_source`・`framedLimitConePiZeroEquiv_source`・
`framedLimitHomPiZeroEquiv_source` は元の始域の射の局所化像による前合成と両立する。
`framedLimitDerivedHomEquiv_source` により導来 Hom 同値の始域自然性も成立。
`localizedConstantDiagram` と `localizedFramedLimit` は同じ弱同値の普通の局所化への降下。
`framedLimitAdjunction` は両者の局所化圏全体での実際の随伴。
`framedLimitAdjunction_homEquiv_comparison` は元の両対象の像へ戻すと
既存の `framedLimitDerivedHomEquiv` を回収することを保証する。
`HomotopyWeight.conePoint`・`coneClass` は元の重み付き族から同じ錐の零単体と類を作る。
`constantDiagramSourceClass_eq_coneClass` は既存の始域の類を同じ随伴族で表示し、
`constantDiagramHomEquiv_comparison_app` は全単体で元の augmentation の後合成を回収する。
`framedLimitConeClass` は同じ通常の錐の右族から作る既存の右錐空間の類。
`framedLimitHomPiZeroEquiv_coneClass` はその像が元の `coneToFramedLimit` の局所化像となる式。
`strictConeFamilies_mixed` は元の両族の混合 Hom 内での厳密な一致。
`sourceRightConeComparisonIso_strictClass` はその同じ類を右の単体図式表示の錐へ移す。
`coneSpaceReindexIso_point`・`coneSpaceReindexIso_class` は元の添字移送の零単体と類の保存。
`rightSimplicialConeIso_coneClass` と `sourceRightConeComparisonIso_coneClass` は、
元の通常錐の類そのものの一致を保証する。
`framedLimitDerivedHomEquiv_cone` は元の錐の射の局所化像を、
同じ `coneToFramedLimit` の局所化像へ送る全体の正規化。
`framedLimitAdjunction_homEquiv_cone` は局所化随伴でも同じ比較射を回収する。
`FrameHom.AdjointRightDerived` は前合成随伴と局所化の完全忠実性から、
任意の候補関手への自然変換の同値と左 Kan 拡張の普遍性を構成する。
`framedLimitDerivedComparison` は元の `limitComparisonNatTrans` を局所化して作る比較。
`localizedFramedLimit_isRightDerivedFunctor` は同じ比較を持つ一般小図式の右導来極限性。
`limitFunctor_hasRightDerivedFunctor` は存在、`framedLimitDerivedIso` は任意の右導来関手の値との同型。
`carrierRightFrame_cofibrant`・`carrierRightFrame_homotopicallyConstant` は
同じ右 frame の底での Reedy cofibrancy とホモトピー定値性。
`carrierFramedLimitProbeFunctor` は任意の複体の関手的な cofibrant 試験始域で、
`carrierFramedLimitConeSpace` は同じ右 frame と重みで作る実際の Kan 錐空間。
`carrierFramedLimitHomPiZeroEquiv` はその π₀ と、元の任意の複体から
`framedLimitFunctor` の実際の底への局所化 Hom の同値。
`carrierFramedLimitHomPiZeroEquiv_mapClass` は実際の複体射から作った類で元の局所化像を回収する。
`CarrierDiagram.projectiveModelCategory` は任意の小圏上の複体図式の具体的な射影モデル。
I・J の自由図式像の小対象性は sphere・零複体の有限表示性から証明し、
J-cell の非循環性は評価の余極限保存で証明する。局所表示可能性の追加仮定は不要。
`CarrierDiagram.constantDiagramReplacement` と `constantDiagramFrame` は
元の複体に関手的な定値図式の cofibrant 置換と全次数の frame。
`CarrierDiagram.constantDiagramSourcePiZeroEquiv` はその重み付き錐の π₀ と
元の定値図式からの局所化 Hom の同値で、終域図式の射に自然。
`CarrierDiagram.constantDiagramSourcePiZeroEquiv_class` は元の図式射の局所化像を回収する。
`Diagram.forget_isRightQuillen` は具体的な両図式モデル間の忘却の右 Quillen 性。
`carrierRightSimplicialFrameFamily` は同じ右 frame の底の単体的表示。
`carrierRightSimplicialConeComparisonIso` はその Hom の錐と既存の底の右錐の自然同型。
`carrierSourceRightConeComparisonIso`・`carrierSourceRightConeComparisonNatIso` は
同じ複体の始域 frame と元の右 frame の底を混合 Hom で結ぶ比較で、元の図式射に自然。
`carrierFramedLimitConePiZeroEquiv` は底の右錐の π₀ と元の定値複体図式からの
忘却図式への局所化 Hom の同値で、終域図式に自然。
`carrierFramedLimitDerivedHomEquiv` はこれを合成した、任意の複体から
元の計算対象の底への局所化 Hom と定値複体図式の局所化 Hom の同値。
`HomotopyWeight.realizationMap_eq_lan` は元の mate による実現の係数射と
同じ Yoneda 左 Kan 拡張の係数射の一致。
`framedLimitCarrierIso_naturality`・`framedLimitCarrierNatIso` は元の底の計算同型を
実際の図式射に自然に束ねる。成分は既存の `framedLimitCarrierIso` そのもの。
`carrierFramedLimitHomPiZeroEquiv_target` と `carrierFramedLimitDerivedHomEquiv_target` は
底への Hom 比較と底の導来 Hom 同値の、元の図式射による後合成への自然性。
`carrierFramedLimitConeBifunctor` と `CarrierDiagram.constantDiagramSourceBifunctor` は
底の右錐と始域錐を元の複体に反変な関手として保持する。
`carrierSourceRightConeComparisonIso_source` は同じ混合 Hom の錐比較の始域自然性。
`carrierFramedLimitConePiZeroEquiv_source`・`carrierFramedLimitHomPiZeroEquiv_source` は
元の複体射の定値図式の局所化像・元の複体射の局所化像による前合成と両立する。
`carrierFramedLimitDerivedHomEquiv_source`・`carrierFramedLimitDerivedHomEquiv_both` により、
底の導来 Hom 同値は始域にも自然で、両変数の元の射を同時に移す式を持つ。
`carrierStrictConeWeightedFamily` は任意の複体を頂点とする通常錐の全単体の族。
`carrierStrictConeFamilies_mixed` と同じ Kan 錐比較・添字移送による類の計算から、
`carrierFramedLimitDerivedHomEquiv_cone` は元の錐の局所化像を、実際の
`carrierConeToFramedLimit` の局所化像へ送る。
`weightedCotensorCarrierHomEquiv_app` は同じ Kan 拡張保存同型の単位整合を使う
随伴の全単体の計算。`carrierConeToFramedLimit_forget` は忘却した E 代数錐で
この比較が既存の `coneToFramedLimit` の底そのものであることを示す。
`carrierFramedLimitDerivedHomEquiv_forgetCone` は元の代数比較の底の局所化像を回収する。
`ComplexLimits` は任意の複体図式上で、具体的な右 frame・重み付き end と
擬同型不変性、定値複体図式との局所化随伴を構成する。
`ComplexLimits.localizedFramedLimit_isRightDerivedFunctor` は元の通常極限比較による
右導来普遍性で、`ComplexLimits.framedLimitDerivedIso` は任意の右導来極限の値との同型。
`carrierFramedLimitComparisonIso` と `carrierFramedLimitComparisonNatIso` は、
忘却した図式のこの計算と元の E 代数計算対象の底との同じ自然同型。
`carrierFramedLimitComparisonIso_cone`・`carrierFramedLimitComparisonIso_forgetCone` は
元の通常錐・元の E 代数錐の比較射の局所化像を保つ。
`framedLimitCarrierDerivedIso` は底の任意の右導来極限の値との比較。
一般 homotopy 極限の右導来普遍性と底の導来比較まで構成済み。
`mappingSpace` は実際の関手的分解から作る E 代数の Kan な導来写像空間 Map^h。
`mappingSpacePiZeroEquiv` は任意の普通の局所化後の Hom と π₀ の同値で、始域・終域の射に自然。
`mappingSpaceClass` は元の代数射から作る実際の零単体の類で、比較は局所化で元の同じ射になる。
`mappingSpace_map_both_isIso` は両変数の擬同型を任意の anodyne 反転後に同型へ移す。
`FrameHom.frameChoiceIso` は共通 frame による比較を反転した二変数の自然同型。
`sourceFrameHom` は元の終域への Kan な Hom、`sourceFrameHomComparisonIso` は選んだ Map^h との自然同型。
これらにも単体集合の完全なモデル構造の入力仮定はない。
E2a-4・5 は完了。
E2b は Dwyer–Kan 型の自由単体的局所化で進める。
`CofibrantAlgebra` と `cofibrantAlgebraWeakEquivalences` は具体的な cofibrant 相対圏。
`cofibrantAlgebraReplacement` は既存の関手的置換そのもので、包含と両側の自然な擬同型を持つ。
`cofibrantAlgebraHoEquivalence` は同じ包含と置換による普通の局所化の同値。
`cofibrantAlgebraMappingSpace` は元の Kan Map^h の制限で、その π₀ は同じ相対圏の局所化 Hom。
`cofibrantAlgebraMappingSpacePiZeroEquiv_class` は元の代数射の局所化像を回収する。
`SimplicialLocalization.freeRelativeComonad` は指定する矢だけからなる列の自由相対圏の
余単位・対角・余結合性・両余単位則を束ねる。
`freeResolutionLevel` と augmentation・外側の面・退化およびその恒等式は全次数で構成済み。
`cofibrantAlgebraRelativeCategory` は Hom の宇宙を対象の宇宙 u+1 へ揃えた具体的な DK 入力。
`cofibrantAlgebraDKForgetRelative` は底の cofibrancy を要求せず全複体へ忘却する相対関手。
`discreteAlgebraDKFunctor` は元の離散 E 代数を同じ関手的置換でこの入力へ送る。
`freeResolution` は既存の汎用 comonad 解像へ代入した、通常の単体圏上の全自由相対圏の解像。
`cofibrantAlgebraFreeResolution` と同じ augmentation は全作用素を持つ具体的な E 代数の入力。
`strictLocalizationMap` と `strictLocalizationFunctor` は元の構成的な局所化の厳密な
因子化・一意性で恒等関手と合成を等式として保つ。
`localizedFreeResolution` と `cofibrantAlgebraLocalizedFreeResolution` は全自由次数を
局所化した単体的な圏の図式で、元の普通の局所化への augmentation を持つ。
`localizedFreeResolutionObjectEquiv` は augmentation の対象写像の全単射性による同じ対象の表示。
`localizedFreeResolutionObject_naturality` は全単体作用素が元の対象の表示を保つ式。
`localizationHom` は同じ局所化 Hom を固定対象の単体集合へ束ねる。
`localizationComposition`・`localizationIdentity` と `localizationEnrichedCategory` は
元の次数ごとの合成・単位による厳密な豊穣構造と全公理。
`KanLocalizationCategory` は同じ有限積保存 Ex∞ による Kan 化で、全 Hom は実際に Kan。
`kanLocalizationUnit` は元の Ex∞ の単位による厳密な豊穣関手で、Hom の比較は anodyne。
`localizationNerve` は既存の γ1 を代入した Mathlib の coherent nerve で、quasicategory。
`BarrattEccles.CAlg_R` はこれを実際の cofibrant E 代数相対圏へ代入した quasicategory。
`cAlgVertexEquiv`・`cAlgVertex`・`discreteCAlgVertex` は元の対象・同じ置換・離散対象の頂点。
`FrameHom.ComonadResolution.resolutionMap` は一般の comonad 解像の全作用素に自然な係数射。
`freeResolutionFunctor` と `localizedFreeResolutionFunctor` は同じ自由解像の係数関手。
`localizedFreeResolutionMap_augmentation` と `localizedFreeResolutionMap_object` は
元の augmentation と対象表示の係数自然性を証明する。
`localizationEnrichedMap` は同じ Hom の係数写像の単位・合成保存を束ねる。
`kanLocalizationEnrichedMap` と `localizationNerveMap` は同じ Ex∞ と coherent nerve への延長。
`localizationNerveMap_vertex` は元の係数の対象写像を頂点で回収する。
`BarrattEccles.complexRelativeCategory` は Hom の宇宙だけを揃えた全複体と擬同型の相対圏。
`cAlgForgetLocalization` は CAlg_R からその具体的な局所化の quasicategory への忘却射で、
`cAlgForgetLocalization_vertex` は同じ置換の底の複体を回収する。底の cofibrancy は要求しない。
`localizationHomMap_id/comp` と `localizationEnrichedMap_id/comp` は元の係数の厳密な関手則。
`kanLocalizationEnrichedMap_id/comp` は同じ Ex∞ での関手則、
`localizationHomKanUnit_naturality` は元の anodyne 単位の係数自然性。
`localizationNerveFunctor` は相対圏から同じ局所化の coherent nerve への関手。
`localizationHomAugmentation` は全 augmentation の固定 Hom への同じ比較。
`LocalizationComponents` は元の DK Hom の π₀ を射とする圏で、
`localizationComponentsAugmentation` は同じ普通の局所化への比較関手。
`localizationArrowZero`・`localizationArrowClass` は元の射の一文字の列による零単体とその類。
`localizationComponentsAugmentation_arrow` は同じ射の Q による局所化像を回収する。
`localizationResolutionWordEdge` は元の自由な列とその合成の一文字の列を結ぶ実際の辺。
その空列・二文字への代入から恒等・合成則を証明し、`localizationComponentsQ` を構成。
`zeroLevelComponentsFunctor` は形式逆を含む零次の全射を同じ DK Hom の類へ送る。
`localizationComponentsLift` は指定弱同値を反転する同じ生成関手の持ち上げ。
`localizationComponentsEquivalence` は元の augmentation と同じ持ち上げの両逆による圏同値。
`localizationComponentsQ_isLocalization` は普通の圏としての局所化の普遍性を与える。
`localizationHomPiZeroEquiv` と `kanLocalizationHomPiZeroEquiv` は実際の raw・Kan Hom の π₀ を
同じ普通の局所化 Hom と同定し、元の射の類の Q への正規化も保持する。
`FrameHom.ULiftRelativeLocalization` は同じ up・down の厳密な局所化による Hom 宇宙の比較。
`BarrattEccles.cofibrantAlgebraDKPiZeroEquiv` と `cofibrantAlgebraKanDKPiZeroEquiv` は
元の cofibrant E 代数の既存 Map^h と raw・Kan DK Hom の π₀ の同値で、
各 `_class` は元の同じ代数射・単位・零単体の類の照合を与える。
`FrameHom.ArrowSpan` は指定した両脚を持つ三本矢の圏。
`FrameHom.SpecialHammock` は実際の trivial fibration・trivial cofibration を両脚に使い、
全縦射の弱同値性を両脚と二つのうち三つから証明する。
`frameElementSpanFunctor` は元の cosimplicial Hom の全単体と全作用素を同じ三本矢へ送る。
`frameSpanSourceComparison`・`frameSpanTargetComparison` は元の比較射による自然変換。
`chosenResolutionSpanFunctor` は元の chosenResolutionHom の同じ二つの分解への代入。
`SpecialHammock.valueFunctor` と `chosenResolutionSpanValue_zero` は元の局所化射と π₀ 比較の照合。
`mappingSpaceSpecialHammockFunctor`・`mappingSpaceSpecialHammockNerveMap` は任意の可換環上の
同じ Map^h の全単体の図式と、その Hom の宇宙だけを揃えた要素圏の nerve からの実際の射。
`FrameHom.SimplexTerminalAugmentation` は反対要素圏の列の終端単体への尾を使い、
最終頂点を消す面も含む全作用素に自然な元の単体集合への augmentation を構成する。
`SimplexTerminalNerve.augmentation_localized_isIso` は任意の単体集合で同じ射の
anodyne 反転後の可逆性を証明する。標準単体の収縮、境界の貼合せ、骨格余極限を使い、
単体集合のモデル構造を要求しない。反対 nerve の実同型は KST/ProExcision から再利用する。
`NerveULiftHom.iso` と `SimplexTerminalNerve.liftedAugmentation` は同じ射の宇宙比較。
`BarrattEccles.mappingSpaceIndexAugmentation` は右射と同じ始域から元の Map^h への左射で、
`_localized_isIso` は任意の可換環上で反転性を与える。
`mappingSpaceSpanComparison_vertex` は全次数の単体を表す頂点で両射が
元の π₀ 同値と同じ局所化射を与えることを証明する。
特殊な三本矢への右射の反転性と、その nerve と既存 DK Hom の高次比較は未証明。
`FrameHom.FrameLift` は既存の LiftSpace の全単体を元の持ち上げ三角形と同定し、
その反対要素圏と分解の comma 圏の同値を構成する。
元の fiber の射影は全単射の右持ち上げ性を持ち、その収縮と終端 augmentation から
全 comma 圏の nerve の元の終射を anodyne 反転後に同型へ送る。
`FrameHom.resolutionOverFunctor` は同じ分解から自明 fibration の slice への関手で、
`resolutionCommaTerminal_image_isIso` は全ての指定終点の comma 圏の可縮性を与える。
`BarrattEccles.mappingResolutionCommaTerminal_localized_isIso` は任意の可換環上の
同じ Map^h の分解への代入。単体集合モデルや元の代数の cofibrancy の入力は不要。
この分解側の asphericity から三本矢の右射全体への余終性の適用は後続。
`FrameHom.AnodyneWeakDetection` は元の anodyne 局所化での反転性を、全 Kan 標的への
元の内部 Hom の π₀ の反変関手により F1b の弱同値・弱可縮性へ移す。
`NerveAsSmall.iso` と `AsSmallComma.equivalence` は同じ元の射列と可換三角形の宇宙比較。
`NerveQuillenA.nerveMap_isLeftCofinal` は F1b の通常の comma と native な slice の
実同型・Quillen A を再利用する。
`smallResolutionOverFunctor_isLeftCofinal` と
`BarrattEccles.mappingSmallResolutionOverFunctor_isLeftCofinal` は同じ分解図式の nerve の
left cofinality を与え、各 `_isWeakHomotopyEquivalence` は同じ射の弱同値を与える。
対象と Hom の持ち上げの前後で、元の関手の全作用は `AsSmallComma.smallFunctor_up` と可換。
三本矢の全図式への余終性の適用と右射そのものの反転性は未証明。
`ArrowSpan.commaEquivalence` は元の両脚の slice と中間 Hom による全三本矢の表示。
`costructuredArrowDiagram` は右脚に沿う後合成の全 Cat 値図式で、厳密な恒等・合成則を持つ。
`CommaGrothendieck.equivalence`・`ArrowSpan.grothendieckEquivalence` は元の三射を使う
明示的な順逆による全図式の表示で、右脚の slice の恒等右脚は始対象。
`BarrattEccles.mappingSpaceSpanGrothendieckNerveMap_fac` は同じ Map^h の元の右比較射を
全図式の nerve を経由して全単体で厳密に回収する。
回収射は anodyne 反転後に可逆で、元の右射の反転性は
`mappingSpaceSpecialHammockNerveMap_localized_isIso_iff` により同じ中間射へ帰着される。
`mappingRightHomDiagram_map_localized_isIso` は全 E 代数の fibrancy を使い、
全右脚の全遷移に対する元の frame Hom の不変性を証明する。
右脚の Hom の不変性と分解の比較を合わせる工程は後続で、右射全体の反転性は残る。
`costructuredArrowProjection_rightFibration` と `costructuredArrowPre_isPullback` は
固定右対象の元の比較が分解図式の right fibration に沿う引き戻しであることを証明する。
`resolutionFixedRightComparison_isLeftCofinal` と
`BarrattEccles.mappingResolutionFixedRightComparison_isLeftCofinal` は同じ分解の余終性を
全固定右対象の比較へ移す。始域の図式は `smallResolutionOverFunctor_leftForget` により
元の frame の全対象・全作用素を厳密に回収する。
`leftCofinal_localized_isIso` は元の left anodyne・trivial Kan 因子分解と実際の収縮を使い、
同じ余終な射を anodyne 反転後に可逆とする。単体集合モデルは要求しない。
`mappingFixedRightDiagramComparison` は全右脚に自然な同じ比較で、
各 `_isLeftCofinal`・`_localized_isIso` は全成分の余終性と同じ反転性を与える。
`mappingFixedRightGrothendieckComparison` はこの自然変換からの全図式の比較関手。
`CommaPreLeft.projection` と `canonicalSection` は全図式の比較の各 comma を
分解側の comma へ射影し、元の右成分による `contraction` で収縮する。
`CommaPreLeft.comparison_isLeftCofinal` はこの収縮と Quillen A による全図式の余終性。
`fixedRightGrothendieckComparison_toComma` は元の Grothendieck の比較との厳密な整合で、
`BarrattEccles.mappingFixedRightGrothendieckComparison_localized_isIso` は同じ全図式の
比較そのものを anodyne 反転後に可逆とする。成分ごとの結論だけからは推論しない。
`FrameHom.BarRows.isColimit` は元の `BarConstruction.rows` の転置した各行を、
同じ基底射列の最初の値の余積として表示する。`map_localized_isIso` はこの余積と
モデル構造不要の対角比較を使い、成分ごとの反転性を元の bar 関手の射へ移す。
`BarrattEccles.mappingRightHomFromIdentity` の各成分は元の指定右脚による後合成。
`mappingRightHomFromIdentity_bar_localized_isIso` は恒等右脚の始対象性と全遷移の
不変性から、同じ定値図式から全 Hom 図式への bar 比較の反転性を与える。
固定右脚の nerve と bar の比較、その比較を経由する元の右射の因子分解は後続。
比較の構成は [Low, §3.2〜3.7](https://arxiv.org/pdf/1409.8062)（Dwyer–Kan §7 の整理）を参照。
DK と既存 Map^h の高次の単体集合の比較・∞ 局所化の普遍性、
忘却先と既存 D(R) との比較、離散対象の ∞ 関手と離散性・極限保存・G1′ は未完成。

原典：
[Berger–Moerdijk 2003](https://arxiv.org/pdf/math/0206094)、
[Berger–Fresse 2004](https://arxiv.org/pdf/math/0109158)。
