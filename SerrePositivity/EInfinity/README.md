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
`FrameHom.ConstantBar.augmentation` は定値図式の元の bar から最初のラベルへの射。
元の各行の要素圏を始対象に収縮し、`augmentation_localized_isIso` で反転性を証明。
`FrameHom.BarRows.valueInclusion_localized_isIso` は始対象を持ち全遷移が反転される
図式の各値の包含そのものを反転する。指定対象は始対象に限らない。
`BarrattEccles.mappingRightHomBarInclusion_localized_isIso` は任意の指定右脚への代入。
`mappingSpaceBarInclusion` は元の Map^h と同じ fibrant 置換の右脚を使い、
全単体で元の右脚とラベルを一定の射列に送る。`_localized_isIso` も証明済み。
`mappingSpaceIndexBarMap` は元の全単体の共通始域から同じ bar への比較で、反転可能。
`FrameHom.Thomason.map` は元の nerve の bar から Grothendieck 全図式の nerve への射。
全単体作用素と係数の自然性を証明し、`valueInclusion_map` は同じ fiber の包含を厳密に回収。
`map_localized_isIso` は同じ宇宙の小圏を値に持つ任意の図式で同じ射の反転性を証明。
`map_isWeakHomotopyEquivalence` は同じ元の射を F1b の弱ホモトピー同値へ移す。
添字・fiber の宇宙を独立にした射の構成と、反転性の同じ宇宙の仮定を区別する。
`FrameHom.CommaNerve.contraction` は元の最後の頂点による comma 射列の復元と収縮。
`barProjection_localized_isIso` は任意の p : E → D で、comma 図式の bar から元の
E の nerve への射影の反転性を与える。値と添字の宇宙は独立で、モデル構造は不要。
`BarrattEccles.mappingResolutionBarComparison_localized_isIso` は元の分解から全左脚への
全右脚の比較を bar でも反転する。`mappingResolutionThomasonSquare` は同じ元の
Grothendieck 比較と bar 比較が二つの Thomason 射で厳密に可換であることを示す。
`Thomason.transportComparison` は comma 図式から元の図式への厳密に自然な移送。
`transport_localized_isIso` は各成分を元の恒等脚の包含と移送の単位で反転する。
`commaTotalTransport` は全図式の忘却から同じ移送への自然変換で、
`commaMap_forget` は同じ Thomason 射の後の忘却を元の comma bar 射影と照合する。
これらと元の自然性の正方形・bar の成分不変性から、Thomason 射の反転性を導く。
`mappingResolutionThomason_localized_isIso`・`mappingSpanThomason_localized_isIso` は
元の全右脚の分解側・全左脚側の二つの小さい図式への実際の代入。
`Thomason.fiberNerveMap_localized_isIso` は始対象を持ち全遷移の nerve が反転される
図式で、同じ元の各 fiber の包含を反転する。
`CosimplicialHomElements.equivalence`・`smallEquivalence` は元の Hom の反対要素圏と
同じ cosimplicial 図式の comma 圏の明示的な順逆で、右対象にも厳密に自然。
`SimplexTerminalNerve.map_localized_isIso` は元の終端 augmentation から反対要素圏の
nerve の不変性を移す。`SmallNerve.map_localized_isIso` で宇宙を揃え、
`CosimplicialHomElements.smallCommaMap_localized_isIso` が同じ小さい comma の比較へ移す。
`BarrattEccles.mappingSmallResolutionRightDiagram_map_localized_isIso` と
`mappingResolutionFiberNerveMap_localized_isIso` は元の全右脚の遷移と固定 fiber の包含への代入。
`mappingSpaceResolutionFiberEquivalence` は元の Map^h と同じ置換の右脚での同値。
`mappingSpaceResolutionFiberNerveMap` は同じ共通始域の Hom と対象の宇宙を揃えて
元の固定 fiber へ送る。`mappingSpaceResolutionGrothendieckNerveMap` と
`mappingSpaceSmallSpanGrothendieckNerveMap` は同じ分解の全図式と全左脚・全右脚への
比較で、それぞれ `_localized_isIso` を証明。全次数で元の中間射を保持する。
`SmallCommaGrothendieck.equivalence` は元の両脚・中間射・左右の射の up/down による
明示的な同値。`BarrattEccles.mappingSmallSpanRecoveryNerveMap` は同じ小さい全図式から
元の特殊な三本矢への回収で、局所化後に可逆。
`mappingSpaceSmallSpanGrothendieckNerveMap_fac` は元の右比較射そのものを全単体・全作用素で
厳密に回収する。左脚の augmentation ≫ 𝟙 と、射の恒等射を正規化して証明する。
`mappingSpaceSpecialHammockNerveMap_localized_isIso` と `_isWeakHomotopyEquivalence` により、
同じ元の右射の反転性と弱ホモトピー同値性は完成。三本矢の nerve の Kan 性は要求しない。
`mappingSpaceIndexAugmentation_isWeakHomotopyEquivalence` は同じ左射の弱同値性。
`mappingSpaceSpecialHammockComparisonIso` は同じ二射で定める Map^h の宇宙拡大と三本矢の
anodyne 局所化後の同型で、`_fac` は元の左射の後の像が元の右射であることを照合。
`FrameHom.WeakThreeArrow` は元の弱同値の両脚を持つ三本矢の圏で、全縦射の弱同値性も
元の両脚と可換性から導く。`ArrowSpan.inclusion` は脚の類を広げる充満忠実な包含。
`WeakThreeArrow.LeftReplacement.functor` は左脚の関手的分解と中間射の pushout、
`RightReplacement.functor` は右脚の関手的分解と pullback により元の三本矢を置換する。
同じ `unit`・`counit` を `FullyFaithfulNerveRetraction` で包含元にも戻し、
`WeakThreeArrow.inclusion_localized_isIso` と `_isWeakHomotopyEquivalence` により
特殊な三本矢の元の包含の反転性・弱同値性を証明。始域の cofibrancy は要求しない。
`BarrattEccles.algebraSpecialThreeArrowInclusionNerveMap_localized_isIso` は元の実際の
二つの関手的分解への代入。`mappingSpaceWeakThreeArrowNerveMap` は元の同じ共通始域からの
比較で、`_localized_isIso`・`_isWeakHomotopyEquivalence` を証明。
`mappingSpaceWeakThreeArrowComparisonIso` と `_fac` は同じ元の二射による局所化後の同型。
`Hammock.Word` は空語を含む有限の向き付き語、射は色を保つ単調写像。
`Hammock.Zigzag` は固定語・固定端点の zigzag と全縦弱同値の圏で、
`Hammock.graph` はその nerve。後ろ向きの列には元の弱同値だけを要求する。
`Zigzag.postcompose` は相対関手を全列・全縦射へ作用させ、恒等・合成にも厳密に整合。
`Hammock.ThreeArrow.equivalence` は同じ三列の zigzag と元の三本矢の圏同値。
順関手は元の四頂点・三射を保持し、逆向きの対象の回収では端点の等式だけを移す。
`BarrattEccles.algebraHammockGraph` は任意の可換環上の実際の弱同値を使う graph。
`mappingSpaceHammockGraphNerveMap_localized_isIso` と `_isWeakHomotopyEquivalence` は
同じ元の共通始域から三列の graph への比較の反転性と弱同値性。
`mappingSpaceHammockGraphComparisonIso_fac` は同じ元の二射との整合。
`Word.Hom.cut` は列の写像に沿う頂点の切断。`lt_cut_iff`・`fiber_iff` は初期区間と
元の fiber を特徴付け、`cut_zero`・`cut_last`・`cut_id`・`cut_comp` は全端点と合成の整合。
`Direction.category` は元の圏または反対圏で、`Segment.chain`・`map` は同方向の区間の合成。
`map_allowed` は後ろ向きの合成の弱同値性、`map_refl` は空区間と元の恒等射の一致。
`Segment.forward_map_comm`・`backward_map_comm` は元の全縦射との可換性。
`WordAction.functor` は任意の色を保つ単調写像の fiber ごとに列を合成する遷移関手。
全頂点の切断位置の縦射を保持し、始点・終点と後ろ向きの弱同値を保持する。
`BarrattEccles.algebraHammockTransition`・`algebraHammockGraphMap` は同じ元の E 代数の
弱同値への代入であり、モデル instance の追加入力や大域化は不要。
`Segment.chain_restriction` は小区間と大区間の射列の制限の厳密な一致。
`map_adjacent` は元の一列の射の回収、`map_comp` は二つに分割した区間の合成則。
`WordAction.segment_obj` は圧縮後の区間合成を元の切断間の区間合成と同定する。
`functor_id`・`functor_comp` は語の恒等・合成と元の全遷移関手の厳密な整合。
`Hammock.categoryDiagram`・`graphDiagram` は全語・全単調写像の実際の図式。
`colimitGraph`・`graphInclusion` はその単体集合の余極限と元の標準射。
`colimitGraphDesc`・`graphInclusion_desc`・`colimitGraph_hom_ext` は余極限の普遍性。
`BarrattEccles.algebraHammockGraphDiagram`・`algebraHammockColimitGraph` は同じ E 代数への代入。
`algebraHammockGraphCocone_isColimit` は元の全標準射の余錐の実際の余極限性。
`mappingSpaceHammockColimitNerveMap` と `mappingSpaceHammockColimitComparison_fac` は
元の同じ Map^h の共通始域・左射・三列の比較を保持した、全語の余極限への比較。
`Word.appendFunctor` は全語と全単調写像の連結関手。`cut_append_left`・`cut_append_right` は
左右の全頂点の切断を、元の二つの切断と照合する。
`ZigzagAppend.obj`・`map`・`functor` は共有端点を一つにする全対象・全縦弱同値の連結。
`joint_app_heq` は元の固定端点の条件から接合点の縦射の整合を導く。
`NerveProduct.iso` は元の射列の積と射影を全作用素で使う、明示的な nerve の二項積同型。
`graphComposition` は二つの固定語の graph の積から連結語の graph への単体的射。
`BarrattEccles.algebraHammockGraphComposition` は任意の可換環上で同じ元の全頂点・全縦射を保持。
`emptyObj`・`graphUnit`・`colimitUnit` は元の空語から固定語の graph と全語の余極限への単位射。
`algebraHammockGraphUnit`・`algebraHammockColimitUnit` は同じ実際の E 代数への代入。
`Word.Block` は一定の列番号差の連続部分、`Word.leftBlock`・`rightBlock` は実際の連結の両側。
`Segment.chain_block`・`map_block_heq` の連続部分比較を実際に代入した
`ZigzagAppend.map_left_heq`・`map_right_heq` は元の左右の全区間合成を回収する。
`vertex_naturality`・`arrow_naturality`・`app_naturality` は全頂点・全列・全縦射を照合。
`ZigzagAppend.functor_naturality` は元の連結関手と全語の遷移の厳密な自然性。
`graphComposition_naturality` は全語の graph 図式に対する元の単体的合成の自然性。
`pairDiagram`・`compositionPairingCocone`・`colimitCompositionPairing_fac` は全語の対の
積図式と、同じ合成射に整合する余錐・その余極限からの比較・元の各成分の回収。
`BarrattEccles.algebraHammockGraphComposition_naturality` と `algebraHammockCompositionCocone`・
`algebraHammockColimitCompositionPairing_fac` は同じ任意の可換環上の実際の余錐への代入。
`tensorPairCocone_isColimit` は二つの元の余錐に `IsColimit.tensor₂` を適用した余極限性。
`tensorPairColimitIso` は対の図式の余極限と二つの余極限の積との標準同型で、
`_fac` は全固定語の元の標準射の積を回収する。
`colimitComposition`・`colimitComposition_fac` は実際の二つの余極限の積からの合成と
全固定語の対上での元の合成の回収。`tensorPair_hom_ext` は同じ標準射の積による一意性。
`tensorPairColimitIso_comp` は前工程の比較を同じ標準同型と合成に厳密に分解する。
`BarrattEccles.algebraHammockColimitComposition` と `_fac`・
`algebraHammockTensorPairColimitIso`・`_fac`・`_comp`・`algebraHammockTensorPair_hom_ext` は
任意の可換環上の同じ元の E 代数への代入。単体集合のモデル構造は不要。
`Word.empty_append`・`append_empty` は元の列の方向を保つ語の単位等式。
`ZigzagAppend.empty_left_functor`・`empty_right_functor` は元の全対象・全縦射での
連結と単位遷移の合成の厳密な恒等則。`graphComposition_left_unit`・`_right_unit` は
全単体での単位則。`colimitComposition_left_unit`・`_right_unit` は同じ元の空語の
`colimitUnit` と実際の余極限上の合成の左右単位則で、`_fac` は全固定語の回収。
`BarrattEccles.algebraHammockColimitComposition_left_unit`・`_right_unit` と各 `_fac` は
任意の可換環上で同じ元の合成と単位に対して成り立つ。
`Word.append_assoc` は三つの元の語の全方向を保つ結合等式。
`ZigzagAppend.obj_assoc_heq`・`map_assoc_heq` は元の三部分の全頂点・全列・全縦射を照合し、
`functor_assoc` は元の語の等式による遷移後の厳密な関手の一致。
`graphComposition_assoc` は全単体の結合則。`tensorTriple_hom_ext` は外部積余錐の反復で
得る三つの実際の余極限の積からの一意性。`colimitComposition_assoc` は同じ元の合成の結合則。
`Hammock.enrichedCategory` は全語の実際の余極限・空語の単位・元の連結の合成を持ち、
左右単位・結合の全公理を満たす明示的な単体的豊穣圏。
`BarrattEccles.algebraHammockEnrichedCategory`・各 `_hom`・`_id`・`_comp` と
`algebraHammockColimitComposition_assoc` は任意の可換環上の同じ元の E 代数への代入。
大域モデル instance や単体集合のモデル構造は追加しない。
`Word.Hom.cut_image_castSucc`・`cut_image_succ`・`cut_surjective` は単射な語の射の
元の列の両端と全頂点の回収。`WordAction.arrow_image_heq`・`obj_injective`・
`functor_faithful` は元の列の回収・対象単射性・全縦射の忠実性。
`NerveEmbedding` は N の小圏版の nerve の単射性を `AsSmall` と同じ元の射列で
異なる対象・射の宇宙へ移す。`graphDiagram_map_mono`・`_app_injective` は
元の全語の図式の単射な遷移が全次数で単射であることを示す。
`BarrattEccles.algebraHammockGraphMap_mono`・`_app_injective` と
`algebraHammockTransition_obj_injective`・`_faithful`・`_image_arrow_heq` は
任意の可換環上で同じ元の E 代数への代入。
`Word.Hom.cut_empty_fiber`・`WordAction.empty_fiber_arrow_heq` は像の外の列が
同じ元の頂点の恒等列であることを示す。この二つには語の単射性も不要。
`WordAction.column_eqToHom_of_cut_eq` は挿入恒等列を元の端点の移送として回収し、
`app_cut_eq` は同じ切断の全 fiber 上で元の縦射の成分が異種等しいことを示す。
この二つには語の単射性は不要。
`embeddingPreimage`・`map_embeddingPreimage`・`embeddingPreimage_map` は
包含の像の間の全縦射の回収と両逆で、`functor_full` は元の遷移の充満性。
`nerveChainLift_comp`・`nerveMap_range_iff` は充満忠実な関手の元の全射列を持ち上げ、
全単体の像を各頂点の対象の像で特徴付ける。
`graphDiagram_map_range_iff` と `BarrattEccles.algebraHammockGraphMap_range_iff` は
同じ元の全語の graph 図式と任意の可換環上の E 代数への代入。
`algebraHammockTransitionPreimage`・`_map_preimage`・`_preimage_map`・
`algebraHammockTransition_full` は同じ元の全縦射の厳密な回収・両逆・充満性。
`IdentityColumn`・`IdentityOutside` は元の隣接頂点の等式と元の恒等移送の条件。
`identityFiber_vertex` は条件を満たす任意の対象の同じ切断 fiber 上の頂点を同定し、
`IdentityPreimage.obj` は像の列を元の二端点へ移して原像を構成する。
`IdentityPreimage.obj_image`・`WordAction.obj_range_iff` と
`graphDiagram_map_range_iff_identityOutside` は元の対象と全単体の像の完全な特徴付け。
`Word.subword`・`intersectionInclusion_range` は元の列の有限集合の交わりの部分語。
`graphDiagram_intersection_range` は同じ元の部分複体の像の交わりとの等式。
`ProperDiagram` は Dwyer–Kan §4.4 の二条件で、`graphDiagram_proper` は §5.4 の
元の全語の図式への適用。`ProperDiagram.intersectionComparison_isIso`・`_fac` は
元の交わりへの標準包含そのものの同型性と元の包含への一致。
`BarrattEccles.algebraHammockGraphDiagram_proper`・`algebraHammockIdentityPreimage_image`・
`algebraHammockGraphIntersectionComparison_isIso`・`_fac` は任意の可換環上で完成。
`Word.erase`・`eraseInclusion_missing_iff` は元の一列を削除した部分語とその包含。
`eraseSimplex`・`_fac`・`_unique` は全行恒等の一列を除いた元の全射列の一意な回収で、
`eraseSimplex_map` は全 face・degeneracy に対する厳密な自然性。
`Word.mergeMap`・`_surjective`・`_fiber` は同方向の隣接二列だけをまとめる元の全射。
`RawHammock` は元の語と全射列の依存和で、`RawHammock.simplicialSet`・`augmentation` は
元の全作用素と同じ余極限への標準射を保持する単体集合と単体的射。
`Reduction.merge`・`erase` は元の二つの基本縮約。`length_lt`・`chain_value_eq` は
長さの減少と同じ元の余極限内の値の保存。`Reduction.map`・`chain_map` は全作用素での保存。
`reduced_iff_no_reduction` は原典の交互方向・非恒等列の条件との一致。
`exists_reduced_representative`・`exists_reduced_same_value` は全次数の元の有限回の縮約で
同じ値を持つ縮約済みの代表へ到達することを示す。
`BarrattEccles.algebraHammockRaw_existsReducedRepresentative`・`_existsReducedSameValue`・
`algebraHammockRawReduction_map` と元の raw 単体集合・射は任意の可換環上で完成。
`identityColumn_obj_image_iff`・`eraseSimplex_identityColumn` は元の恒等列の包含による反映と
一列を削除した後の他の恒等列の保存。
`Word.embedding_eq_of_range` は同じ列の像を持つ包含の元の語と写像の一意性。
`raw_eq_of_embeddings` は元の包含後に同じ全射列を与える未縮約対象を厳密に同定する。
`Word.erase_composite_range`・`doubleErase_image` は二重削除の元の列の像と全射列の回収。
`erase_erase_join` は削除同士の各側0〜1段の局所合流で、同じ列と異なる列の両方を含む。
`BarrattEccles.algebraHammockEraseSimplex_fac`・`algebraHammockEraseRaw_reduction`・
`algebraHammockEraseErase_join` は任意の可換環上で同じ元の基本縮約への代入。
`Word.target_eq_of_surjective` は同じ列の全射から終域の色と語の等式を回収する。
`raw_eq_of_surjections` は二重合成の結果を、元の語を含めて厳密に同定する。
`Word.merge_left_remaining_color`・`merge_right_remaining_color` は他方の合成に必要な色を回収し、
`merge_predAbove_comp` は元の単体圏の二重全射の合成則を照合する。
`merge_merge_join` は同じ位置・接した位置・離れた位置とその逆順を含め、
合成同士の各側0〜1段の元の同じ未縮約対象への合流を与える。
`BarrattEccles.algebraHammockMergeRaw_reduction`・`algebraHammockMergeMerge_join` は
任意の可換環上の元の基本合成と同じ合流。モデル構造は局所的に選ぶ。
`Word.punctureInclusion` は Fin.succAbove による同じ元の一列の補集合の包含。
`erase_raw_eq_of_embedding`・`erase_reduction_of_embedding` は一列を除く任意の包含を
既存の元の基本削除と照合する。`punctureSimplex_fac`・`_raw_eq` は元の全単体を回収する。
`merge_erase_overlap_eq` は合成する二列の一方を削除する場合の厳密な相殺。
`Word.descendSurjection` は元の全射から色保存を回収し、`merge_erase_join_of_square` は
面・退化の可換四角形から各側一段の合流を得る。`merge_erase_join` は左右外側も含む全場合。
`reduction_local_join`・`reduction_church_rosser` は二つの基本操作と有限縮約全体の合流性。
`reduced_representative_unique` は同じ元の対象から到達した縮約済みの代表の一意性。
`normalForm`・`_chain`・`_reduced` は有限縮約で得る元の一意な代表で、`_eq_iff_join` は
同じ正規形と有限縮約による共通対象の存在の同値。`normalForm_map_normalForm` は
元の全作用素の後の再縮約への整合。`reducedSimplicialSet` はその再縮約を全作用素とする
元の縮約済み対象の単体集合。`normalization`・`reducedAugmentation` と
`normalization_augmentation` は元の未縮約対象からの単体的正規化と同じ元の標準射の回収。
`BarrattEccles.algebraHammockReducedRepresentative_unique`・`algebraHammockNormalForm_map`・
`algebraHammockNormalization_augmentation` 等は任意の可換環上で完成。
`Word.factorMerge` は元の隣接等像の二列の合成を先に行う厳密な分解。
`Word.factorEmbedding` は元の包含の像への厳密な持ち上げで、欠けた一列の包含を分離する。
`normalForm_transition` は始域・終域の長さの和での帰納により、空語も含め任意の元の語の
遷移が同じ正規形を与えることを示す。全単射の場合も元の raw の等式で照合する。
`graphNormalization`・`_naturality` は同じ固定語の正規化からなる元の全語の余錐。
`colimitNormalization`・`graphInclusion_colimitNormalization` は元の余極限からの射と
各固定語の標準射の後の回収。`colimitNormalization_augmentation`・
`augmentation_colimitNormalization` は元の全単体の両逆。
`reducedColimitIso` は Dwyer–Kan §5.5 の元の余極限と縮約 hammock の実同型。
`_hom_fac` は元の固定語の標準射と正規化への一致、`_inv` は同じ元の標準射への一致。
`rawAugmentation_colimitNormalization` は既存の元の raw 正規化を回収する。
`BarrattEccles.algebraHammockNormalForm_transition`・`algebraHammockReducedColimitIso`・
各 `_hom_fac`・`_inv`・`algebraHammockRawAugmentation_colimitNormalization` 等は
任意の可換環上で完成。
`Word.LengthBounded`・`lengthInclusion` は元の全射も保持する長さ制限の全部分圏。
`lengthStage`・`lengthStageTransition` は元の制限図式の余極限と上限を増やす標準射。
`lengthDiagram`・`lengthCocone_isColimit`・`lengthColimitIso` は、長さ段階を Nat に沿って
余極限に取ると同じ元の全語の余極限になることを証明する。proper 性は不要。
`lengthColimitIso_fac` は元の段階の標準射への一致。
`lengthStageMap`・`lengthDiagramMap` と `lengthColimitIso_naturality` は、元の図式の
自然変換に対する全段階の整合と、同じ元の `colim.map` そのものの回収。
`BarrattEccles.algebraHammockLengthColimitIso`・`_word_fac` と
`algebraHammockLengthReducedIso`・`_word_fac` は任意可換環上の実際の長さ濾過と
元の全語・縮約 hammock の標準射への一致。
`Word.IsAlternating`・`alternating_cases` は空語も含む二つの初期方向による分類。
`alternating_ne` は正の長さの二つの語の区別。`IsAlternating.map_injective`・
`length_le`・`target_eq_of_length_le` は交互方向語からの全写像の単射性・長さ増大と、
同じ長さでは元の語の等式と元の射の一致まで回収する。
`Word.intersectionLeft`・`intersectionRight` と各 `_fac` は元の列の交わりの因子分解。
`ProperDiagram.overlap_lift` は同じ像の二つの単体を元の交わりから同時に回収する。
`overlap_lengthStage` は短い語の元の段階でそれらの像が一致することを示す。
`lengthBoundary` は短い語の包含の像の和。`BoundaryPresentation` は元の表示で、
`lengthBoundaryStageValue_eq` は選択に依存しない元の段階の値を回収する。
`lengthBoundaryToStage` は前の段階への実際の射。`lengthBoundary_square` は上の段階への
元の標準射との可換性。境界の添字図式の余極限と像の和を無証明に同一視しない。
`BarrattEccles.algebraHammockLengthBoundaryToStage_app`・`algebraHammockLengthBoundary_square`・
`algebraHammockAlternatingGraphMap_mono` は任意可換環上で完成。
`Word.merge_cone` は元の二つの基本合成を短い語で比較する厳密な可換余錐。
`Word.TopStage`・`topStageInclusion` は前段階の全語と最大長の交互方向語の全部分圏。
`topMergeArrow_zigzag`・`topStage_comma_connected` は元の structured arrow 圏の連結性で、
`topStageFinal` は同じ包含の Final 性。任意の射は元の隣接等像から基本合成を経由する。
`topStageColimitIso`・`_fac` は元の段階の余極限の回収と同じ固定語の標準射への一致。
`Word.toImage`・`imageInclusion`・`toImage_fac` は元の列の像への全射と元の包含への分解。
`imageWord_length_le` は短い語から最大語への任意の射を境界で扱うための長さの上限。
`BarrattEccles.algebraHammockTopStageColimitIso`・`_fac`・`_toColimit_fac` は任意可換環上で完成。
`lengthBoundaryLift`・`_ι`・`_toStage` は元の短い語の包含の境界を経由する射と回収。
`Word.MaximalAlternating` は元の長さ n+1 の交互方向語の部分型で、
`maximalAlternatingEquiv` は二つの初期方向との同値、`maximalAlternating_finite` は有限性。
`StageAttachmentData` は前段階と元の最大語の射の境界上の整合条件。
`stageAttachmentComponent_naturality` は元の全射を含む全写像への整合を証明する。
`stageAttachmentDesc`・`_lower`・`_upper`・`_unique` は同じ元の次段階からの一意な延長。
`stageBoundarySum`・`stageTopSum` は元の境界と最大語の余積。
`stageBoundaryAttach`・`stageBoundarySumInclusion`・`stageTopInclusion` は元の標準射。
`lengthStagePushout_isColimit`・`lengthStage_isPushout` は proper 図式の元の次段階の
境界による pushout の普遍性（Dwyer–Kan §4.3 の適用に要る形）。
`BarrattEccles.algebraHammockLengthStage_isPushout`・`algebraHammockStageBoundaryAttach_fac`・
`algebraHammockStageTopInclusion_fac` は任意可換環上で同じ元の標準射への代入。
`trivialKanFibration_pre_of_mono_weak` は単射の弱同値の Kan 標的への前合成を反転する。
`weakPushout_mono`・`weakPushout_other_mono` は元の弱同値または相手側が単射の
元の pushout による弱同値保存。元の対象に Kan 性は課さない。
`weak_underPushout_map`・`weakPushout_fixed_base` は相対写像円柱による元の固定境界の比較。
`weakPushout_gluing` は二つの元の pushout の三成分の比較から残りの弱同値を得る。
`mapSubcomplex` は元の全体の射の制限。`weakUnion_gluing`・`weakFiniteUnion` は
交わりを保つ部分複体族の元の有限和の弱同値の貼り合わせ。全体の射の弱同値性は不要。
`BoundaryPresentation.map`・`lengthBoundaryMap`・`_ι`・`_lift`・`_attach` は
元の自然変換を境界へ制限し、元の包含と貼り合わせ射・段階の比較を回収する。
これらは単体集合のモデル構造を入力にしない。Kan 標的への前合成の反転を使用し、
任意の弱同値が全 quasicategory 標的への前合成同値を満たすとは扱わない。
`weakRangeMap` は単射の像への元の比較の弱同値性を与える。
`subsetImage_inf` は proper 図式の列部分集合の像が交わりを保つことを表す。
`lengthBoundary_eq_finsetSup` は元の長さ境界と card≤n の列部分集合の有限和の等式。
`weakLengthBoundaryMap` は proper 図式間の成分ごとの弱同値から、
同じ `lengthBoundaryMap` 自身の弱同値性を導く。境界の Kan 性・比較の単射性は不要。
`stageBoundarySumMap`・`stageTopSumMap` は元の余積の比較。
`stageBoundarySumMap_inclusion`・`_attach`・`stageTopSumMap_inclusion` は四辺の自然性。
`stageBoundarySumInclusion_mono` は境界包含側の単射性。
`weakTwoIndexCoproduct` は二つの初期方向で添字づけた元の余積の比較の弱同値性。
`weakLengthStageMap_succ` は境界包含側を単射として `.flip` した pushout を貼り、
前段階への貼り合わせ射の単射性を要求しない。
`lengthZeroIso` の逆射は元の空語の標準包含。`weakLengthStageMap` は全有限段階の帰納。
`weakSequentialColimitMap` は対象・射の宇宙を持ち上げて F2 の filtered 補題を適用し、
同じ元の Nat 図式の `colim.map` の弱同値性を証明する。
`weakProperColimitMap` は proper 図式間の成分ごとの弱同値を元の全語の余極限へ移す
（Dwyer–Kan §4.5）。Π の filtered 性・元の値の Kan 性・単体集合のモデル構造は不要。
`Word.forwardFunctor` は元の forward 列の部分語を取り、`forwardMap_fac` は
元の包含への厳密な因子分解。`forwardInclusionNat` は同じ包含の自然変換。
`Word.sandwichFunctor` は左右の語を固定した列追加。`paddingFunctor` は
backward 一列ずつを両端に付け、`paddingInclusionNat` は元の中央列の包含。
`forwardMap_intersection_range`・`sandwichMap_intersection_range` は元の列の像の交わり。
`ProperDiagram.precomp` は単射とこの交わりを保つ語関手への proper 性の保存。
`ProperDiagram.padding`・`paddedForward` は二つの実際の前合成への適用。
`paddingDiagramMap`・`paddedForwardDiagramMap` の成分は元の包含の像である。
`Word.forwardInclusion_isIso`・`forwardMap_forwardInclusion` は全方向 forward の
固定対象の元の同型性と冪等性。`forwardCollapseNat` は元の一列への唯一の合成。
`forwardColimitCocone_isColimit`・`forwardColimitIso`・`_fac`・`_inv_fac` は
任意の値の圏での元の余極限の普遍性と元の標準射への一致。
`Word.padding_single_forward` は元の三列の語の等式。
`paddedForwardColimitIso`・`_fac`・`_inv_comparison` は元の三列と同じ比較射を回収する。
`paddingColimitMap_retraction` は元の padding 余極限の射の左逆。
`paddedThreeComparison`・`_fac`・`_retraction`・`paddedForwardColimit_comparison_recovery` は
同じ元の比較から元の全語の三列の標準射を厳密に回収する。
一般の値の圏での `colimMap` は、単体集合で同じ元の `colim.map` に一致する。
`ThreeArrow.Padding.outerFunctor`・`innerFunctor`・`middleFunctor` は元の5列の三配置。
`toOuterNat`・`toInnerNat` は元の左右の弱同値の脚を一頂点で使う二つの自然変換。
`outer_action_functor`・`inner_action_functor` は元の WordAction との厳密な一致。
元の列と切断位置の表から、全頂点・全列・全縦射を照合する。
`toOuterHomotopy`・`toInnerHomotopy` は同じ nerve のホモトピー。
`original_maps_image_eq` は anodyne を反転する関手の下で元の graph の二写像を同定する。
`colimit_comparison_image_eq` は同じ元の三列の標準射の後の padding 比較と、
`paddedThreeComparison` の像の一致。単体集合モデルや元の nerve の Kan 性は不要。
`ForwardPath.pullbackPath`・`pushoutPath` は元の任意長の forward 射列の同時置換。
終点・始点も動かす comma 圏を添字とし、`pullbackFunctor`・`pushoutFunctor` は
元の全対象・全射での関手性と二つの射影・包含への一致を持つ。
`pullbackEndpointIso`・`pushoutEndpointIso` の射は元の snd・inl であり、
元の置換射への一致と元の全比較への自然性を証明する。
`pullbackProjection_trivialFibration`・`pushoutInclusion_trivialCofibration` と
`pullbackComparison_weakEquivalence`・`pushoutComparison_weakEquivalence` は
元の全頂点の自明性と全縦弱同値の保存。モデル圏の left/right proper 性は不要。
`terminalBlockInput`・`initialBlockInput` と各 `Comparison` は元の zigzag の
同じ forward 区間・元の端点・全縦射への代入。区間の等式の移送も保持する。
`normalizedPullbackPath`・`normalizedPushoutPath` は、元の終点・始点の同型を
標準の `Functor.copyObj` で移し、指定対象を端点に持つ射列へ正規化する。
`normalizedPullbackFunctor`・`normalizedPushoutFunctor` は動く端点も含めて関手的。
正規化後の射影・包含は元の置換射を端点成分で回収し、全比較に自然である。
`normalizedPullbackProjection_trivialFibration`・
`normalizedPushoutInclusion_trivialCofibration` と各 `Comparison_weakEquivalence` は
正規化後も全頂点の自明性・全縦弱同値を保持する。長さ零も含む。
`Zigzag.MovingHom` は局所端点も動く全縦弱同値を記録する。
`ZigzagAppend.Moving.map`・`fixedMap` は接合点の成分が一致する全縦射を貼り、
全体の端点にだけ固定条件を要求する。恒等・合成と全成分の回収も証明する。
`ForwardPath.normalizedPullbackZigzag`・`normalizedPushoutZigzag` は実際のブロック。
`pullbackLeftBoundary`・`pushoutRightBoundary` は元の外側の backward 射に
射影・包含を合成し、外側の端点を保つ。全縦比較と内外の端点成分も保持する。
`MiddleBackward.pullbackProjection` は中央の因子分解を左へ伝えた全体から元の
同じ語の zigzag への実際の射。`pushoutInclusion` は中央の自明 cofibration を
指定中間対象の恒等列にした同じ語の zigzag への実際の射。左右の長さ零も含む。
`MiddleBackward.Factorization.projection` は同じ指定関手的分解を代入した成分。
`MiddleBackward.Family` は元の左右射列の関手と三つの自然な脚・全縦弱同値を記録する。
`zigzagFunctor` は元の全体の関手であり、恒等・合成を同じ全成分で検証する。
`Family.Hom.natTrans` は左右の自然な比較を全体の実際の自然変換へ移す。
`pullbackInputs` は同じ指定関手的分解による comma 図式であり、
`pullbackFunctor`・`pullbackCounit` は左置換の全体の関手と元への自然変換。
`pullbackMiddle_trivialCofibration` は正規化後の中央の自然な脚の自明性。
`pushoutFunctor`・`pushoutUnit` は中央が自明 cofibration の図式の右置換と自然変換。
`MiddleBackward.Extract.family` は元の固定語の zigzag 圏からブロック図式を抽出する。
`rebuilt_eq` は元の全頂点・全列の厳密な回収、`rebuildFunctor_eq` は
元の全縦射も含めた恒等図式との等式。Family を外部入力にはしない。
`MiddleBackward.TrivialCofibration` は中央の実際の列が自明 cofibration の全部分圏。
`replacement`・`counit` は同じ元の包含と元の恒等図式に対する関手的置換。
`inclusion_localized_isIso`・`inclusion_isWeakHomotopyEquivalence` はその包含自身の
nerve の反転性・弱ホモトピー同値性。同じ指定分解から、長さ零も含めて証明する。
`Word.insertBetween` は二つの元の語の間に一列だけを挿入する元の単射。
`InsertBetween.action_obj_eq` はその WordAction と、同じ左右の zigzag の間に
恒等列を置いた実際の対象の厳密な一致。元の cut・全頂点・全列で検証する。
`MiddleBackward.IdentityInsertion` は元の中央 backward 挿入と全部分圏への持ち上げ。
`preimageObj`・`originalFunctor_obj_preimage` は右置換の各対象の実際の前像。
`rightReplacement`・`rightReplacementCompIso` は全忠実性による関手の持ち上げ。
`unit` から第二の包含を反転し、第一の包含との合成により
`graphMap_isWeakHomotopyEquivalence` は元の graphDiagram.map 自身の弱同値性を得る。
`eraseIso`・`eraseIso_hom_fac` は元の eraseInclusion と同じ列の像による因子分解。
`erasedGraphMap_isWeakHomotopyEquivalence` はその元の削除語の標準射の弱同値性。
両端 backward・二つの任意長の forward ブロックの間の中央列について証明済み。
`Zigzag.MovingDiagram` は両端の評価関手が動く局所図式。連結・自然な縦比較と
全体の両端を固定した関手・自然変換への回収を備える。各評価・各列の自然性、
両端の自然同型・全縦弱同値の回収も証明済み。
`MiddleBackward.MovingFamily` は動く局所端点を保つ左右の射列と三つの脚。
元の関手的分解による左右置換、射影・包含の自然性と counit/unit を持つ。
`ZigzagAppend.Part` と `MovingDiagram.leftPart/rightPart` は元の任意の前後の部分を抽出。
`MovingDiagram.append_parts` は全対象・全縦射を保った元の図式への厳密な回収。
`MiddleBackward.MovingExtract.family` は動く局所図式からの抽出。
`rebuildDiagram_eq` は全対象・全縦射を含む元の局所図式との厳密な等式。
`MiddleBackward.Context` は元の任意の前後の語を切り出し、局所置換を貼る。
`rebuiltFunctor_eq` は元の全体の恒等関手への厳密な回収。
`pullbackOriginalCounit`・`pushoutOriginalUnit` は元の全体の恒等図式との自然な比較。
`Context.TrivialCofibration.inclusion_isWeakHomotopyEquivalence` は元の全体の中央列が
自明 cofibration の全部分圏への包含自身の弱同値性。任意の前後の語で第一工程は完了。
`MovingFamily.precomp`・`MovingDiagram.precomp` は端点の評価関手も含めて制限する。
`Context.TrivialCofibration.rightReplacement/rightUnit` は同じ全部分圏上の右置換と unit。
`rightReplacement_identity` は元の全体の同じ中央列が実際の恒等列であること。
`Context.Erasure` は元の eraseInclusion の WordAction を使用する。
`preimageObj`・`originalFunctor_obj_preimage` は既存の恒等列による像の特徴付けから、
元の右置換の実際の前像と厳密な対象の回収を与える。本質像への所属は証明済み。
`rightReplacementCompIso`・`unit` で第二の包含を反転し、第一の包含と合成する。
`graphMap_isWeakHomotopyEquivalence` は任意の前後の語を持つ元の中央 backward 列の
元の eraseInclusion の graph 写像自身の弱同値性。左右の長さ零も含む。
`Word.BackwardBounds` は指定 backward 列の両隣の最も近い backward 境界。
`whole_eq`・`middle_column_cast` は元の語と指定列を保つ厳密な局所分解。
`paddedBackwardBounds` は padding の両端で必要な境界の存在を保証する。
`paddedBackwardInsertion_isWeakHomotopyEquivalence` は元の padding.map eraseInclusion。
`paddedBackwardEmbedding_isWeakHomotopyEquivalence` は backward 列だけを欠く任意の
元の単射への有限挿入。`paddedForwardDiagramMap_isWeakHomotopyEquivalence` は元の
自然変換の全成分、`paddedThreeComparison_isWeakHomotopyEquivalence` は proper 余極限
による元の padded な三列の比較の弱同値性。
`paddingColimitMap_isWeakHomotopyEquivalence` は元の左逆と全 Kan 標的への Hom の
π₀ の全単射性から従う。任意の弱同値の anodyne 局所化後の可逆性は仮定しない。
`threeArrowGraphInclusion_isWeakHomotopyEquivalence` は元の三列の標準射自身の弱同値性。
`BarrattEccles.mappingSpaceHammockColimitNerveMap_isWeakHomotopyEquivalence` は任意可換環の
元の Map^h の共通始域から元の全語の余極限への右射を同じ実モデルと分解で反転する。
`Zigzag.Relative.functor` は元の相対関手による固定語の全対象・全縦射の写像。
`chain_eq`・`segment_map_heq` と `wordAction_functor_eq` は元の全 fiber の合成と
恒等列の挿入との厳密な両立。モデル構造は要求しない。
`Hammock.Relative.graphDiagramMap`・`colimitMap`・`reducedMap` は同じ相対関手の
全語の自然変換・余極限の写像・元の縮約同型による reduced hammock の写像。
元の標準射・正規化・augmentation への一致と、恒等・合成則を備える。
`threeArrowNormalization_isWeakHomotopyEquivalence` は元の三列の正規化の弱同値性。
`BarrattEccles.algebraReducedHammock`・`algebraHammockReductionIso` は元の実 E 代数への代入。
`mappingSpaceReducedHammockNerveMap` は元の Map^h の同じ共通始域からの右射で、
元の augmentation への回収式と弱ホモトピー同値性を持つ。
`Zigzag.EndpointChange.functor` と `Zigzag.Relative.fixedFunctor` は元の端点の等式だけを
移し、元の全頂点・全列・全縦射を保持する。恒等・合成と全語への自然性は厳密。
`FixedObjectDiagram.zigzagDiagram/graphWordDiagram` は対象表示を保つ相対圏の図式から
元の全語・全相対作用素の二方向の図式を構成する。元の相対 augmentation から
`categoryWordAugmentation/graphAugmentation/hammockAugmentation` も自然に得る。
`freeResolutionObject_naturality` は元の自由相対解像の augmentation の対象単射性から
全作用素の対象の等式を回収する。`freeResolutionObject_generator` は同じ標準生成対象。
`freeHammockResolution` は各自由次数の元の全語の余極限である二重単体的図式。
`freeHammockAugmentation` は元の hammock への自然な比較である。
`freeHammockDiagonal`・`freeHammockDiagonalAugmentation` は元の対角とその左射、
`freeHammockDiagonalReduction` は元の reduced hammock への同じ左比較。
`Zigzag.Value.value` は forward 列を Q.map、backward 列を元の wIso の逆射として
評価する。全縦射・全語の合成と恒等列の挿入に不変であり、`colimitValue` は元の全語の
余極限から定数 Hom への評価。相対関手・後合成・固定端点の等式移送への自然性も証明済み。
`FixedObjectDiagram.LocalizationObjects.hammockEvaluation` はこれを全相対作用素で束ねる。
`freeResolutionObject_localized` は既存 DK Hom の対象との一致を証明し、
`freeHammockHomComparison` は元の全自由次数から既存の局所化 Hom への自然な右比較。
`freeHammockDiagonalComparison` はその対角で、既存 `localizationHom` を標的とする。
`freeHammockHomComparison_fac` は元の各語の標準射で同じ評価を回収する。
任意可換環の既存の DK 入力にも代入済み。左右の比較射の弱同値性は未完成。
`MarkedGenerators.homEquiv` は指定生成矢の自由射列と元の W.paths の射の全単射。
`MarkedGenerators.equivalence` は同じ自由圏と元の指定矢の部分圏の圏同値で、
`toWide_inclusion` は元の包含への因子化。恒等射の一文字も空列とは区別して保持する。
`GeneratorPartition.existsUnique_extension` は指定・非指定の生成部分の関手の貼り合わせの
普遍性。共通対象表示の等式を移送し、元の Paths C への拡張の存在と一意性を証明する。
`inverts_iff_markedRestriction` は W.paths の反転と指定生成部分の全射の反転の同値。
`freeResolutionMarkedEquivalence/freeResolution_existsUnique_extension` は元の全自由次数への
代入。これらは比較補題2.3の自由積による帰着の準備であり、弱同値性の証明は後続。
`GeneratorBlocks.Form` は空でない単色ブロックを交互に連ねた標準形で、最終色と端点を
添字に持つ。`normalize/flattenNormal/equivalence` は元の射列と標準形の互いに逆な全単射。
`existsUnique_normal` は元の全生成文字を保持する標準形の存在と一意性。
`typedBlock` と `inclusion_typedBlock` は各ブロックを元の二つの自由因子の射へ移して戻す。
`normalize_monochrome` は空でない単色列を一ブロックにし、元の恒等文字は空列に潰さない。
`GeneratorBlocks.comp/categoryEquivalence` は元の連結・単位・結合則と両立した圏同値。
`freeResolutionBlockEquiv/freeResolutionBlockCategoryEquivalence` は元の全自由次数への代入で、
元の射・恒等・合成を回収する。任意可換環の既存固定端点でも検証済み。
hammock の全行・全縦射の分解と命題3.2の単体的 pushout、比較射の弱同値性は後続。
`GeneratorWord.erase` は元の生成矢の始域・終域・射を保った非指定文字列。
`erase_comp/erase_eq_nil_iff/erase_square` は連結、指定射列の消去とその正確な逆、
元の指定縦射の可換正方形での不変性。`exists_first_of_erase_ne_nil` は指定接頭列・
最初の非指定矢・残りへの元の射列の切断、`erase_first_split` はその文字列の先頭を回収。
`Hammock.UnmarkedGenerators.column_hom/column_row/column_backward` は元の全列・全行への代入。
`GeneratorWord.functor` は文字列の連結を合成とする一対象圏への関手で、指定射列を恒等へ送る。
既存の評価を代入した `UnmarkedGenerators.value/colimitValue/reducedValue` は全語の作用と
正規化に不変で、元の標準射と augmentation を回収する。後ろ向き列の逆射の寄与も空。
`freeHammockGeneratorWordValue` は元の全自由次数・既存固定端点への代入。
各切断の一意性・全縦射の切断・hammock の積分解・弱比較は後続。
`GeneratorWord.initialLength_first_split` は元の射列だけから最初の切断位置を回収する。
`first_split_total/first_split_unique` は同じ先頭 Total 矢と両側の射列の一意性。
`first_split_square/first_split_square_same_arrow` は元の可換正方形を接頭列と残りへ分解する。
`FirstCut` の存在は `firstCut_nonempty_iff`、一意性は `firstCut_ext` で証明済み。
`firstCut` は非空の非指定文字列から選ぶ切断で、`firstCut_erasure` は先頭と残りを回収する。
`column_firstCut_square/column_firstCut_row` は元の全縦射・全行への代入。
`rowFirstCut` は基準行の非空性だけから全行の切断を得る。後ろ向き列には切断は存在しない。
任意可換環の元の全自由次数でも検証。固定生成矢での図式への整列・反復・積分解は後続。
`GeneratorWord.FixedCut.ofFirstCut` は Total 等式から同じ固定生成矢の表示へ戻す。
`FixedCut.square` は元の接頭列・残りの等式であり、追加の自然性は要求しない。
`ColumnCut` の射は元の全縦射。`prefixMap/generatorMap/residualMap` は実際の自然変換で、
`columnMap_factorization` は元の列の厳密な因子化。
`rowCutDiagram` は元の全行を同じ生成矢で表示し、`rowCutDiagram_forget` は元の関手を回収。
`rowPrefix/rowGeneratorMap/rowResidual` と `rowColumn_factorization` は全行の自然な因子化。
`rowSource_eq/rowTarget_eq` は元の端点評価、接頭列・全縦射の指定性も保持する。
任意可換環の実際の全自由次数でも検証。再添字・全語への両立と全体の積分解は後続。
`ColumnCut.lift/lift_forget/lift_ext/lift_precomp` は任意の添字圏の元の図式の持ち上げ、
忘却による回収、切断の選択への独立性、前合成の厳密な両立。
`prefixDiagram/generatorDiagram/residualDiagram/columnDiagram` とそれらの再添字則は
自然変換全体を保持し、`diagram_factorization` は元の列を回収する。
`rowGenerator_simplex` は元の任意の単体作用素による基準行変更でも同じ Total 生成矢を回収。
`rowCutDiagram_simplex` はその表示を移すと元の切断図式の前合成に厳密に一致する。
`rowPrefix_simplex/rowGeneratorMap_simplex/rowResidual_simplex/rowColumn_simplex` は
端点表示を含む自然変換全体の整合。任意可換環の実際の全自由次数でも検証。
全語を切って貼り戻す図式・語の作用への両立・積分解と弱比較は後続。
`Word.ColumnSplit.before/middle/after/whole_eq` は任意列の前後の元の語と同じ一列の
厳密な分解。元の列番号・全方向・全頂点と接合点を回収し、空の前後の語を含む。
`MovingDiagram.changeWord` は全対象・全縦射を保つ語の表示変更で、固定端点では
元の `WordAction` と一致する。`MovingDiagram.ColumnSplit.before/middle/after` は
元の動く端点の全図式の切断で、`recombine_eq/recombinedFunctor_eq` は元の図式・関手を回収。
`before_vertex/middle_vertex/after_vertex` と全縦成分・`middle_arrow` は元の同じ位置への照合。
`UnmarkedGenerators.firstColumn` は最初の非指定列。位置は全縦射・全行で同じで、forward。
`beforeFirstColumn_arrow_mem/beforeFirstColumn_map_mem` は切り出した前の全語の全列・全縦射の指定性。
任意可換環の元の全自由次数でも検証。列内部の切断との接続・W-hammock への回収は後続。
`ForwardZigzag.diagram` は元の自然変換と端点縦射を保つ一列の図式。
`ColumnSplit.sourceJoint_eq/targetJoint_eq` は前後の接合点と元の端点評価の関手の等式。
`Attachments.leftAttachment/rightAttachment` と `attachment_factorization` は列内部の切断を
前後へ接続する。`prefixDiagram/residualDiagram/refinedDiagram` は実際の全語の図式で、
`prefixFunctor/residualFunctor/refinedFunctor` は元の固定端点を持つ。
`AttachedPrefix.arrow_mem/map_mem` は内部の接頭射を含む全 prefix の全列・全縦射の指定性。
`MarkedZigzag.liftFunctor/liftFunctor_inclusion` は全指定図式を元の指定部分圏へ回収して戻す。
`AttachedPrefix.markedFunctor/markedSimplex` は実際の W-hammock の全行・単体で、
包含により元の prefix の全対象・全射を厳密に回収する。任意可換環の全自由次数でも検証。
切断後の全語と単体作用素への整合・積分解は後続。
`Segment.Moving` は端点も動く全縦射に対する元の区間合成の自然性。
`WordAction.movingMap` と `MovingDiagram.wordAction` は元の cut の全縦射を保持し、
固定端点では既存の `WordAction.functor` に厳密に一致する。
`Word.ForwardTriple.collapse` は元の三列から一列への語の射。
`ForwardTriple.segment_composite/column_heq/obj_eq/collapse_append` は元の区間合成と
同じ三射の合成の一列を回収する。`collapse_diagram` は全行・全縦射の厳密な等式。
`Attachments.collapse_blocks` は内部切断の接頭射・生成矢・残りから、元の同じ列の
自然変換を両接合点へ移した全図式を回収する。任意可換環の実際の全自由次数でも検証。
前後の全語の append の括弧を保つ refinedDiagram 全体の回収は以下で完成。
`MovingDiagram.wordAction_append/changeWord_append_assoc` は動く局所端点を含む
全図式の連結自然性・結合則。`Word.fiveBlocksMap` と `wordAction_fiveBlocks` は
元の ((前・左)・中央)・(右・後) の括弧から内部を圧縮し、前後の全語を保持する。
`Attachments.collapsedColumn_eq_middle` は元の middle の表示変更を回収。
`refinementMap/refinedDiagram_recovery/refinedFunctor_recovery` は元の全語・全対象・
全列・全縦射を含む元の τ への厳密な回収。前後の空語も含む。
`refinedSimplex_recovery/refinedSimplex_inclusion` は元の Word 図式の作用と同じ余極限の
標準射で、同じ元の単体を回収する。任意可換環の実際の全自由次数でも検証。
prefix・残りの全単体作用素への整合は以下で完成。全語への整合・反復・積分解は後続。
`firstColumn_simplex` は面・退化で基準行が変わっても同じ最小列の番号を回収する。
`ColumnSplit.*_precomp` は元の語の切断と再添字の整合。
`Attachments.sourceJoint_simplex/targetJoint_simplex/leftAttachment_simplex/rightAttachment_simplex`
と各 block の `*_simplex` は元の接合点・接続自然変換・全縦射を保持する。
`prefixDiagram_simplex/residualDiagram_simplex/refinedDiagram_simplex/refinedFunctor_simplex`
は元の全図式の整合。`refinedSimplex_simplex/refinementMap_simplex` は元の全作用素と同じ圧縮射。
`AttachedPrefix.index_simplex/diagram_simplex/residual_simplex/generator_simplex/functor_simplex`
は実際に選んだ最初の列と因子の再添字を照合する。
`markedFunctor_simplex/markedSimplex_simplex` は実際の指定部分圏の W-hammock へも移す。
端点と語の表示が異なる因子は異種等式、固定端点の refined 全図式・単体は厳密な等式。
任意可換環の実際の全自由次数にも適用。語の作用・reduction・反復・積分解は後続。
`Segment.forward_map_mem/forward_map_split_column/forward_path_map_mem_iff` は
元の同方向区間の指定性・一列の前後での三分割・自由圏での指定性の逆向き。
`column_wordAction_eq_nil_iff` は圧縮後の空文字列を元の fiber の全列で判定する。
`firstColumn_wordAction` は元の最小非指定列の像を圧縮後の最小列へ厳密に照合する。
`firstFiber_erasure_prefix/firstFiber_generator` はその像の列の最初の元の生成矢を保持。
`firstColumn_generator_wordAction/rowGenerator_wordAction` は元の最小列の切断と
実際の全語の図式の単体で選んだ同じ Total 生成矢を厳密に回収する。
空 fiber の恒等列挿入・任意可換環の実際の全自由次数も検証。
prefix・残りの同じ余極限の像の一致、reduction・反復・積分解は後続。
`Segment.toColumn/fromColumn/map_column_factorization` は内部の生の列を挟む元の因子化。
`FixedCut.sandwich/congr/factorization_left/factorization_right/left_heq/right_heq` は
前後の射列と元の端点表示を含む切断の一意性を回収する。
`Segment.forward_cut_left/forward_cut_right` は元の区間合成の切断の前後の射列の厳密な等式。
`WordActionCut.prefixMap/residual/factorization/cut_left/cut_right` は元の圧縮した生の列へ適用。
`FirstFiber.prefixMap_mem/cut_left/cut_right` は実際の最小非指定列の fiber へ代入し、
接頭射・残りを元の切断と前後の元の射列から回収する。後置区間の指定性は仮定しない。
端の空区間・任意可換環の実際の全自由次数でも検証。
前後の語の制限射と全図式の比較、prefix・残りの余極限の像の一致、反復・積分解は後続。
`Word.CutFactor.prefixMap/residualMap` は元の語の射を前後の因子の語へ制限し、
元の列・方向・恒等・合成を厳密に保持する。`prefix_cut/residual_cut` と各 `*_cut_eq` は
前後の全頂点で元の cut と同じ頂点を回収する。空 fiber も含む。
`Attachments.prefix_vertex/residual_vertex/prefix_map_app/residual_map_app` は切断因子を
元の前後の全頂点・全縦射へ照合する。各 `*_action_vertex/*_action_app` は元の語の作用と比較。
`FirstFactorAction.prefix_vertices/residual_vertices/prefix_apps/residual_apps` は最小非指定列で
内部切断端点を含む全頂点・全縦射を保持する。任意可換環の実際の全自由次数も検証。
横の列と切断の接続自然変換の比較、全図式の同定、余極限の像の一致・反復・積分解は後続。
`Word.ColumnSplit.beforeBlock/afterBlock` と `ColumnSplit.before_arrow/after_arrow` は
切断した前後の全列を元の連続部分の同じ列へ回収する。
`before_segment/after_segment` と `Attachments.prefix_segment_before/residual_segment_after` は
前後の全区間合成を元の同じ区間へ照合する。空区間・全方向を含む。
`Direction.block_arrow_heq` と各 `*_direction_arrow/*_direction_before/*_direction_after` は
元の方向付き列を回収する。`prefixCutVertex_block/residualCutVertex_block` は元の cut を保持。
`Attachments.prefix_outer_direction/prefix_outer_arrow/residual_outer_direction/residual_outer_arrow`
は内部切断列以外の全横列と、元の制限射による語の作用の一致。
任意可換環の実際の全自由次数でも検証。内部接続列・全因子図式と同じ余極限の像の
比較は以下で完成。反復・積分解は後続。
`FixedCut.changeGenerator/changeGenerator_left/changeGenerator_right` と
`FirstFactorAction.row_cut_left/row_cut_right` は圧縮後の全行の切断の前後を元へ回収。
`Attachments.prefix_inner_segment/residual_inner_segment` は内部接続列を含む区間の合成を回収。
`prefix_inner_action_arrow/residual_inner_action_arrow/prefix_columns/residual_columns` は残る内部列と
全横列を照合。`prefix_diagram/residual_diagram` は元の全因子図式の異種等式であり、
`prefix_functor/residual_functor` は元の端点表示を移した全関手の厳密な等式。
`EndpointChange.colimitMap/inclusion/image_eq` は同じ元の標準余錐の端点移送。
`prefix_colimit_image/residual_colimit_image` は同じ元の hammock 余極限の像の一致。
`marked_prefix_functor/marked_prefix_colimit_image` は実際の指定部分圏の W-hammock にも適用。
任意可換環の実際の全自由次数でも検証。生成矢の表示を移した各幅での一段の比較であり、
依存和の単体集合の射と全語の非空部分の余極限への降下は以下。reduction・反復・積分解は後続。
`FactorTarget.space` は元の非指定生成矢で指定 prefix と残りの hammock を束ねる単体集合。
`NonemptyGraph.simplicialSet/wordDiagram` は元の非空列を持つ単体の全語の図式。
`FirstFactor.point/point_simplex/point_wordAction` は実際の W-hammock の prefix と残りの
切断点を全単体作用素・全語の圧縮・恒等列の挿入に整合させる。
`cutMap/cutCocone/colimitCut` は元の非空部分の全語の余極限からの切断射。
`inclusion_colimitCut/colimitCut_unique/inclusion_ambientMap` は元の各語の切断・標準射と一意性を回収。
任意可換環の実際の全自由次数でも検証。元の全 hammock の非空部分との同定は以下。反復・積分解は後続。
`nonemptyColumns_wordAction_iff/nonemptyColumns_simplex_iff` は元の非空列条件を保存・反映。
`FirstFactor.detector/ambientMap_detector/ambientMap_injective/ambientMap_mono` は
同じ元の全 hammock 上の検出射と非空余極限の包含の単射性を証明する。
`GeneratorWord.composable_hom_eq_nil_iff` と `edge_column/value_eq_nil_iff/value_ne_nil_iff` は
元の評価・全隣接列・非空非指定文字列の存在を照合する。
`ambientMap_range` は元の包含の像が元の `colimitValue` の非空部分に正確に一致することを証明。
`NonemptyValue.space` はこの元の部分単体集合であり、`nonemptyIso_hom_inclusion` は
全語の非空余極限との同型の後の包含が元の `ambientMap` 自身であることを回収する。
`nonemptyCut/inclusion_nonemptyCut/inclusion_nonemptyIso_val` は元の非空部分上の切断と
元の各語の標準射・切断を回収。任意可換環の実際の全自由次数でも検証。
残りの文字列の tail 式・長さの減少・各次数での有限反復は以下。逆構成・自由積分解は後続。
`GeneratorWord.composable_hom_flatten`・`value_flatten/value_append/value_forward` は
元の全列の順序と貼り戻しの文字列の連結を保持する。
`AttachedPrefix.prefix_value/generator_value/refined_value/value_cons_residual` は全行で元の
指定 prefix の空性・同じ一文字・全図式の回収と生成矢を先頭とする分解を証明する。
`FactorTarget.wordValue`・`point_wordValue/colimitCut_wordValue/nonemptyCut_wordValue` は
実際の切断射と元の余極限の非指定文字列評価の回収式。
`nonemptyCut_generator/nonemptyCut_residual_tail/nonemptyCut_residual_length_lt` は
元の任意の非空点の先頭・残りの tail・厳密な長さの減少を証明する。
`cutRec/cutRec_empty/cutRec_nonempty` は同じ残りの点による長さの依存再帰。
`Spine/spineWithValue/spine_word/spine_empty/spine_nonempty` は各次数の元の指定 prefix と
同じ生成矢を有限回取り出し、元の生成文字列を厳密に回収する。任意可換環の実モデルでも検証。
終端の実際の指定部分圏への同定と反復の全単体作用素への自然性は以下。
貼り戻しとの逆関係と積分解・単体的 pushout は後続。
`AllMarked.Holds/holds_iff/holds_simplex_iff/holds_word_iff` は元の全行・全列の指定性を保存・反映。
`nativeSpace/inclusion/lift/lift_inclusion/lift_reflection/lift_word` は実際の指定部分圏の
hammock と元の包含・全関手の回収と全語の作用への整合。
`detector/inclusion_detector/inclusion_injective/inclusion_mono` は同じ元の包含の単射性。
`holds_value_iff/inclusion_range` は元の全列の指定性と元の評価の空性・包含の像を正確に照合。
`EmptyValue.space` と `AllMarked.emptyIso/emptyIso_hom_inclusion/emptyLift_inclusion/emptyLift_unique`
は元の空文字列部分と実際の指定 hammock の同型・元の点の一意な回収。
`MarkedSpine/markedSpine_word/markedSpine_empty/markedSpine_nonempty` は全 prefix と終端を
実際の W-hammock の点とし、元の同じ生成矢と文字列を保持する。
`MarkedSpine.map/space/wordValue` と `markedSpine_simplex/extraction/extraction_wordValue` は
元の全単体作用素に自然な反復抽出射と元の生成文字列評価の回収。任意可換環の実際の全自由次数でも検証。
元の貼り戻しと抽出の片側の逆関係は以下。逆向きの回収・因子の一意性・自由積の pushout は後続。
`composePoint/composePoint_inclusions/arrowPoint/arrowPoint_simplex` は元の合成と
同じ生成射の一定単体の標準射を各次数で回収する。
`FactorTarget.pastePoint/pastePoint_simplex/paste` は実際の指定 prefix・同じ生成矢・残りを
元の包含と元の hammock 合成で接続する単体写像。
`MovingDiagram.append_fixedFunctor`・`Attachments.generator_fixedFunctor/refinedFunctor_pair` は
元の全図式を同じ三因子の連結関手に回収する。
`FirstFactor.paste_point/cutMap_paste/colimitCut_paste/nonemptyCut_paste` は元の一段の切断を
貼ると元の同じ単体・標準射・非空部分の包含自身に戻ることを証明する。
`MarkedSpine.glue/glue_simplex/gluing` は実際の有限切断列全体の単体的貼り戻し。
`glue_markedSpine/extraction_gluing` は元の全 hammock 上で抽出の後の貼り戻しが元の恒等射。
`extraction_injective/gluing_surjective` は同じ射自身の全次数での単射性・全射性。
任意可換環の実際の全自由次数でも検証。逆向きの貼り戻し後の因子回収・一意性・
積分解・自由積の単体的 pushout・DK の両弱比較は後続。
`colimitValue_composePoint/colimitValue_arrowPoint` は元の合成・生成射の文字列評価を回収。
`FactorTarget.pastePoint_value/paste_value/pasteNonempty` は任意の三因子の貼り戻しの値が
元の生成矢 :: 残りの値であり、元の非空部分へ入ることを証明する。
`markedSpine_native/nativeInclusion_extraction/extraction_gluing_nil` は指定 hammock の元の点を
包含して抽出すると同じ元の終端へ戻ることを証明する。
`Pasted.column_generator/before_column_mem/firstColumn_eq/simplex_firstColumn/simplex_generator` は
元の全指定 prefix・元の一文字・任意の残りを貼った語の最初の非指定位置と同じ生成矢を回収。
`pastePoint_inclusions/nonemptyCut_graphInclusion` は元の標準射と実際の切断の照合。
`pasteNonempty_generator/pasteNonempty_generator_index/pasteNonempty_residual_value` は
任意の余極限の三因子を貼って切ると元の Total 生成矢と残りの非指定文字列を回収する。
任意可換環の実際の全自由次数でも検証。prefix と残りの hammock の点そのものの回収、
逆向きの因子列の回収・一意性・積分解・自由積の pushout・DK の両弱比較は後続。
`GeneratorWord.FixedCut.length_factorization/left_length_of_one/right_length_of_one` は元の
raw な一文字の列の前後の長さ零を回収し、`left_eqToHom_of_one/right_eqToHom_of_one` は
元の端点等式による移送として実際の射を回収する。元の恒等文字と空の射列は区別する。
`zeroNatTrans_eqToHom/zeroNatTrans_heq_id` は全成分が長さ零の自然変換全体を関手の等式の移送へ回収。
`Pasted.column_length_one/selected_column_length_one/cut_left_length_zero/cut_right_length_zero` は
元の貼り戻しの全行で raw な長さを照合する。
`leftAttachment_eqToHom/rightAttachment_eqToHom/sourceJoint_eq/targetJoint_eq` は左右の元の
接続自然変換全体と接合点関手を元の生成矢の端点の定数関手へ回収。
`before_word/after_word/prefix_word/residual_word` は元の前後の語を回収する。
`before_vertex/before_arrow/before_map_app/after_vertex/after_arrow/after_map_app` と
`before_diagram/after_diagram` は元の全頂点・横列・縦射・端点関手を含む前後の全図式の回収。
任意可換環の実際の全自由次数でも検証。長さ零の内部列を恒等列の挿入として標準射へ渡す工程、
prefix と残りの元の hammock の点の回収・逆向きの因子列の回収・積分解は後続。
`Pasted.selected_before_diagram/selected_after_diagram` と
`leftBlock_identity/rightBlock_identity/prefix_identity_diagram/residual_identity_diagram` は
元の選択位置での全切断図式を元の恒等列付き図式へ照合する。
`ForwardZigzag.constant_diagram_fixedFunctor/identity_diagram_fixedFunctor` は任意の射の
定数全図式を回収。`arrowPoint_identity/composePoint_identity_left/composePoint_identity_right` は
元の恒等列の標準射を元の空語の単位点へ戻し、元の左右単位則を回収する。
`prefix_identity_functor/residual_identity_functor` と `EndpointChange.image_heq` から
`prefix_ambient_point/residual_ambient_point` で元の余極限の二点を回収。
`AllMarked.inclusion_endpoint`・包含の単射性から `prefix_native_point/factor_point` を得る。
`FactorTarget.pasteNonempty_cut_point/pasteNonempty_nonemptyCut` は任意の元の三因子の回収。
`FirstFactor.markedSpine_paste/markedSpine_glue/gluing_extraction/markedSpineIso` は
反復抽出と貼り戻しの両逆と元の hammock と全因子列の単体的同型を完成する。
任意可換環の実際の全自由次数へも代入して検証。自由積の単体的 pushout の普遍性・
全指定自由圏の成分の可縮性・命題2.2の左右の弱比較・既存 Map^h との高次比較は後続。
`Zigzag.Relative.append_obj/append_functor` と `Relative.composePoint_map/arrowPoint_map/colimitUnit_point`
は元の相対関手による連結・全余極限の合成・一列・単位の保存。
`AllMarked.nativeComposePoint/nativeUnitPoint` は元の指定部分圏の合成と単位の点。
`inclusion_composePoint/inclusion_unitPoint` は元の包含自身の保存。
`MarkedSpine.prepend/append` は接合点の指定二因子を元の指定 hammock 内で合成する明示的な連結。
`glue_append/extraction_composePoint/composition_gluing` は元の同型の二射の合成保存。
`unitPoint/append_left_unit/append_right_unit/append_assoc/unitMap_gluing` と
`enrichedCategory/degreeCategory` は元の全因子列の豊穣圏・各次数の圏を完成する。
`generatorPoint/glue_generatorPoint/cons_decomposition` は同じ元の生成矢と三因子分解。
`FoldData.fold/fold_append/fold_unique/existsUnique_fold/functor` は指定因子と非指定生成矢の像から
任意の圏への次数ごとの一意な合成保存拡張。
`precompSimplex/fold_simplex/mapTarget/fold_target` は全単体作用素と目標関手への整合。
任意可換環の実際の全自由次数へも代入して検証。豊穣目標の全次数の評価圏と全単体作用素を
束ねた自由積の単体的 pushout の普遍性・全指定自由圏の成分の可縮性・両弱比較は後続。
`EnrichedDegree.category/simplexFunctor` は任意の SSet 豊穣目標の各次数の評価圏と元の全作用素。
`MarkedSpine.EnrichedFoldData` は元の指定 hammock と非指定生成矢の像の指定。
`degreeData/foldPoint/foldPoint_simplex/foldMap/enrichedFunctor` は元の全因子列からの豊穣拡張。
`existsUnique_foldMap/restrictEnrichedFunctor/enrichedFunctorEquiv` は全因子列についての普遍性。
`arrowMap`・`AllMarked.inclusion_unit/inclusion_composition` と
`extraction_unitMap/extraction_composition/extraction_arrowMap/generatorMap_gluing` は
元の hammock 自身と同じ元の生成部分への移送。
`hammockFoldMap/existsUnique_hammockFoldMap/hammockEnrichedFunctor` は元の全語の余極限からの
同じ元の単位・合成を保つ一意な拡張。
`restrictHammockEnrichedFunctor/restrict_hammock_extend/extend_hammock_restrict` と
`hammockEnrichedFunctorEquiv` は任意の豊穣目標について対象写像・元の全 Hom を含む両逆。
任意可換環の実際の全自由次数へも代入して検証。非指定自由部分からの豊穣関手と生成矢の像の
同値への接続・全指定自由圏の成分の可縮性・命題2.2の両弱比較は後続。
`DiscreteEnrichment.enrichedCategory/functorEquiv` は任意の圏の元の離散豊穣化と通常の関手の比較。
`FreeDiscreteEnrichment.functorEquiv` は元の自由圏の離散豊穣関手と生成 quiver の像の全単射。
`EnrichedFoldData.unmarkedEnrichedFunctor/unmarkedEnrichedFunctor_generator/markedEnrichedFunctor`
は元の二つの部分からの関手と同じ元の生成矢の回収。
`EnrichedParts/foldData/parts/enrichedPartsEquiv` は共通対象の表示の等式を保持する関手の組との同値。
`EnrichedHomTransport.point_homOf_heq` は元の等式による Hom の移送を underlying 射へ照合。
`markedInclusionFunctor/unmarkedInclusionFunctor/unmarkedInclusion_generator` は元の二つの包含。
`restrict_marked_comp/restrict_unmarked_comp/restrictParts/freeProductFunctorEquiv` は元の包含との
合成による制限自身の全単射。`freeProductExtension/existsUnique_freeProductExtension` と
`freeProductExtension_marked/freeProductExtension_unmarked/freeProduct_hom_ext` は任意の豊穣目標への
拡張・元の二脚の回収・一意性。DK 命題3.2の自由積の豊穣普遍性をこの形で完成。
任意可換環の実際の全自由次数でも検証。§5.8の全指定自由圏の成分の可縮性と命題2.2の両弱比較、
Map^h の高次比較・∞ 局所化の普遍性は後続。
`FreeQuiverCover.Vertex/quiver/projection/root` は元の自由 groupoid の根からの矢を頂点とする
根付き被覆候補。`forwardTarget/forwardArrow/backwardSource/backwardArrow` は元の矢の持ち上げ。
`starEquiv/costarEquiv/projection_isCovering` は元の star・costar の全単射と被覆性。
`pathStarEquiv/symmetricPathStarEquiv` は元の全有向・対称射列の一意な持ち上げ。
`symmetricEvaluation/coverEvaluation/projected_endpoint/positive_endpoint` は元の商の矢と
実際の持ち上げ終点のラベルの回収。`root_connected` は固定根からの連結性。
`pathProjection/liftPath/liftPath_projection/liftPath_unique/pathProjection_faithful` は元の
正向きの自由圏の関手と実際の射列の一意な持ち上げ・忠実性。
元の全自由次数の指定生成 quiver へも代入して検証。根付き被覆の木性・被覆の元の hammock への
持ち上げ・全指定自由圏の成分の可縮性・命題2.2の両弱比較は未完成。
`FreeQuiverCover.groupoidProjection/groupoidProjection_endpoint` は元の自由 groupoid 間の
射影と全射の終点の式。`fiberSwap/groupoidPostcomposeEquiv` と
`LiftFiber/LiftStar/liftFiberEquiv/generatorPermutation` は持ち上げ射上の可逆な作用を構成する。
`permutationRepresentation/starRepresentation/starPermutation/starRepresentation_action` は
元の自由 groupoid の普遍性から全射の右合成を回収する。
`groupoidProjection_faithful/groupoid_hom_unique/groupoid_isThin` は逆射を含む射影の忠実性と
被覆側の自由 groupoid の薄さ。`root_groupoid_hom_nonempty/groupoid_hom_nonempty/groupoidHomUnique`
は元の二頂点間の射の存在と一意性を提供する。任意可換環の実際の指定生成 quiver でも検証。
木の組合せ的性質・固定端点の hammock の持ち上げ・成分の可縮性・両弱比較は未完成。
`QuiverTree.evaluation/detector/labelValue/path_label/every_edge_in_tree` は対称化した全域木の
木の外の生成辺を整数群で検出し、自由 groupoid が薄い場合に全辺の木への所属を証明する。
`rootPath/height/height_arrow/height_eq_zero_iff/parent_exists/incoming_unique` は元の根からの
射列と高さ・親の存在・入る辺の一意性。`edge_height/edge_toward_higher/higher_incoming_unique`
は全生成辺の高さの差と高い頂点へ入る元の対称生成辺の一意性を保持する。
`IsLeafIn/exists_finite_leaf/exists_nonroot_finite_leaf` は任意の有限頂点集合の葉を選ぶ。
`FreeQuiverCover.spanningTree/every_edge_in_spanningTree/treeHeight/edge_treeHeight` と
`higher_incoming_unique/exists_finite_leaf/exists_nonroot_finite_leaf` はこれらを元の被覆の
証明済みの連結性・薄さへ代入する。根以外があれば根以外の葉を選べる。
任意可換環の実際の全自由次数の指定生成 quiver でも全生成辺の木への所属を検証。
有限部分木の葉の除去を使う hammock の変形・成分可縮性・両弱比較は未完成。
`FreeQuiverCover.pathStar_endpoint/liftPath_endpoint/liftPathTo/existsUnique_liftPathTo` は
ラベルが整合する元の正向き射列を指定両端の間へ一意に持ち上げる。
`DiagramLabels/diagramLift/diagramLift_projection` はラベル付きの元の全図式を持ち上げて戻す。
`zigzagPrefix/zigzagVertex/zigzagPrefix_naturality/zigzagPrefix_arrow` は元の全指定 zigzag の
部分射列の値による全頂点・全縦射・全横列のラベルの整合。
`ZigzagValueFiber/fiberEndpoint/zigzagLift/zigzagLiftMap/zigzagLiftFunctor` は元の値の fiber から
固定根・固定終点を持つ被覆の zigzag 圏への関手で、元の全可換正方形を保持する。
`zigzagLiftFunctor_projection` は持ち上げ後の射影が元の全部分圏の包含に厳密に一致すること。
空語・任意可換環の実際の全自由次数の指定生成 quiver でも検証。
射影後の持ち上げの回収・全語の作用と全単体作用素への整合、有限部分木の縮約による
成分可縮性と元の両弱比較は未完成。
`FreeQuiverCover.projectedPrefix_eq_label/projectedValue_eq/zigzagFiberProjection` は被覆の元の
全頂点のラベルと終点の値 β を回収し、元の値の fiber への射影関手を構成する。
`zigzagLiftFunctor_fiberProjection/zigzagFiberProjection_liftFunctor` は対象・全縦射を含む
両合成の恒等性。`zigzagFiberEquivalence/zigzagFiberCategoryIso` の両関手は元の持ち上げと射影。
`zigzagFiberWordAction` は元の全語の作用の制限そのもので、両関手と厳密に可換する。
`fiberCategoryDiagramIso/fiberGraphDiagramIso/fiberGraphColimitIso` は全語・全単体作用素に
自然な圏値・nerve 図式の同型と、その余極限から被覆の元の hammock への同型。
`fiberGraphColimitIso_fac` は元の各語の標準射の回収。空語と任意可換環の実際の全自由次数も検証。
元の hammock 上の値の fiber と値の fiber の図式の余極限の同定、有限部分木の葉の除去を
使う成分可縮性、元の両弱比較は未完成。
`LabelledColimit.fiber_eqvGen/quotientFiberEquiv/colimitFiberEquiv` は任意の型値図式の自然な
ラベルについて元の余極限と値の fiber を交換する。添字圏の filtered 性は要求しない。
`colimitFiberEquiv_natural/fiberCocone_isColimit` は元の写像への自然性と任意の余極限余錐への移送。
`SimplicialValueFiber.space` は元の単体を保持する fiber、`SimplicialLabelledColimit.colimitFiberIso`
は元の単体集合の余極限との交換同型で、元の各標準射を包含とともに回収する。
`FreeQuiverCover.graphValue/hammockValue/hammockValue_eq_colimitValue` は元の値による評価と
既存の評価との厳密な一致。`fiberGraphIso/fiberValueDiagramIso` は元の各 graph の値の fiber と
全部分圏の nerve の同型を全語・全単体作用素に自然に束ねる。
`valueFiberColimitIso/hammockValueFiberCoverIso/existingHammockValueFiberCoverIso` は元の
hammock 上の値 β の fiber を元の被覆の固定端点 hammock へ同定する。空語・任意可換環の
実際の全自由次数と既存の同じ評価で検証。有限部分木の葉の除去による成分可縮性、
元の両弱比較・既存 DK Hom の高次比較は未完成。
`pathVertices` と `QuiverTree.rootVertices/rootHull/RootClosed` は元の根からの有限射列による
有限包を構成し、祖先への閉性・最小性・単調性・空集合の包を証明する。
`RootClosed.erase_max/parent_mem_of_closed/LeafDeletion/chooseLeafDeletion` は最大高さの葉・
残る親・元の接続辺と除去後の閉性を保持し、頂点数が真に減ることを証明する。
`FreeQuiverCover.finiteHull/finiteHull_closed/finiteHullLeafDeletion` は元の被覆の証明済みの
測地木・薄さへ代入する。`FiniteQuiver.quiver/pathInclusion/subsetFunctor` は元の有限頂点
部分型の生成辺を保持する自由圏の界面で、quiver は局所的に選ぶ。
`LeafDeletion.retractVertex/retractArrow/retractionFunctor` は葉だけを親へ送り、接する辺を
恒等射へ、他の辺を同じ元の生成辺へ送る。`inclusion_retraction` は残りの自由圏上の
厳密な恒等性。`retractionRelative/inclusionRelative` は元の二つの全指定相対関手。
空集合の包・任意可換環の実際の全自由次数と同じ関手の左逆でも検証。
逆順の合成と恒等関手を結ぶ自然変換は下記の通り完成。hammock のホモトピー・成分可縮性・両弱比較は未完成。
`LeafDeletion.collapseFunctor` は元の葉の除去と包含の逆順の合成で、
`collapse_generator_of_ne/collapse_generator_incident` が全生成辺の像を回収する。
`incoming_eq_positive/outgoing_eq_negative/no_outgoing_positive/no_incoming_negative` は
葉に接する元の生成辺と向きを一意に回収する。
`positiveComponent/negativeComponent` は葉では元の接続辺、他では対象の等式による恒等射。
`positiveComponent_generator/negativeComponent_generator` は全生成辺での自然性、
`positiveDeformation/negativeDeformation/deformation` は全射列への自然変換を提供する。
元の接続辺の向きに応じて E→𝟭 または 𝟭→E を選び、成分の回収も証明する。
両方向と元の各成分、任意可換環の実際の全自由次数でも検証。
hammock のホモトピーへの移送・成分可縮性・命題2.2の両弱比較は未完成。
`WeakArrow.sourceCancellation/targetCancellation` は指定射の往復を恒等行へ比較する
実際の二列・一幅の hammock。中間の縦射は元の指定射、両端は恒等射である。
`empty_sourceUnit/empty_targetUnit` が恒等行を空語からの元の挿入へ照合する。
`rowMap/rowHomotopy/colimitRowHomotopy` は任意の元の行と縦射を全次数の単体写像・
ホモトピーに移す。`colimitRowMap_append` は行の連結を既存の豊穣合成へ照合し、
`sourceCompositeHomotopy/targetCompositeHomotopy` が元の往復合成と単位を結ぶ。
`postcomposePointMap/precomposePointMap/composeUnitMaps` は元の一定の点の前後合成で、
元の結合則・単位則とホモトピーの代入も提供する。
`WeakArrow.postSourceHomotopy/postTargetHomotopy/preSourceHomotopy/preTargetHomotopy`
は指定射の forward・backward の前後合成の両逆ホモトピー。
`postcompositionIso/precompositionIso` は任意の anodyne 反転関手での元の二作用の同型。
`postcompose_forward_isWeakHomotopyEquivalence/postcompose_backward_isWeakHomotopyEquivalence`
と `precompose_forward_isWeakHomotopyEquivalence/precompose_backward_isWeakHomotopyEquivalence`
は同じ元の四作用の弱同値性を Kan 標的によって検出する。始終域の Kan 性・モデル構造は不要。
四作用・実際のホモトピー・任意可換環の元の自由解像の全次数でも検証。
相対自然変換による全語の比較は下記の通り完成。成分可縮性・命題2.2の両弱比較は未完成。
`RelativeNatural.movingHom` は元の自然変換の全成分を全列・全縦射の比較へ移す。
`beforeRow/afterRow/beforeFunctor/afterFunctor/component/natTrans` は元の
[id,F(S),ηY]→[ηX,G(S),id] の固定端点の自然変換。
`component_naturality/beforeRow_wordAction/afterRow_wordAction/component_wordAction` と
`beforeFunctor_wordAction/afterFunctor_wordAction` は元の全縦射・全語での厳密な整合。
`graphHomotopy/fixedWordHomotopy/fixedWordHomotopy_wordAction` は同じ区間関手による
全単体のホモトピーと全語への整合。
`beforeMap_recovery/afterMap_recovery/colimitHomotopyMap_fac/homotopy` は元の全語の
余極限上で postηY∘H_F と preηX∘H_G を結び、全標準射と元の既存の両端を回収する。
`homotopy_weak_iff` と四作用の弱同値性から `RelativeNatural.weak_iff` を得る。
`LeafDeletion.collapseRelative/collapse_colimitMap_isWeakHomotopyEquivalence` は
葉を除去して戻す合成を元の全端点の hammock 上の弱同値へ移す。葉が端点でも除外しない。
空語・全語の元の標準射・任意可換環の実際の全自由次数でも検証。
葉の除去と包含自体の各弱比較・有限木の可縮性は下記の通り完成。全被覆の可縮性・命題2.2の両弱比較は未完成。
`weak_middle_of_composites/contractible_of_weak_factor` は元の Kan 標的の反変 π₀ から
二対六則と可縮な因子による可縮性を回収する。
`SubsingletonCategory.row_eq/simplex_eq/colimit_point_eq_unit/colimit_isTerminal` は
一対象で薄い元の圏の全行・全単体・空語からの単位の回収と元の余極限の終対象性。
`QuiverTree.root_no_arrow/root_path_eq_nil/rootPathsSubsingleton/rootPathsThin` は
根だけの元の有限集合に生成辺が無く、元の自由圏が一対象で薄いことを証明する。
`root_colimit_isWeaklyContractible` と `LeafDeletion.collapse_colimitMap_factor/
contractible_of_remaining` を頂点集合の強い帰納で接続し、
`finite_colimit_isWeaklyContractible` が根に閉じた元の有限部分木の全端点を扱う。
`FiniteQuiver.subsetRelative` と `subset_colimitMap_isWeakHomotopyEquivalence`、
`LeafDeletion.retraction_colimitMap_isWeakHomotopyEquivalence/
inclusion_colimitMap_isWeakHomotopyEquivalence` は同じ元の個々の比較射も回収する。
`FreeQuiverCover.finiteHull_colimit_isWeaklyContractible/
finiteHull_subset_colimitMap_isWeakHomotopyEquivalence` は証明済みの元の被覆へ代入する。
根だけ・空集合の包・任意可換環の実際の全自由次数も検証。
全被覆への有限支持と filtered 余極限による移送・命題2.2の両弱比較は未完成。
`FiniteQuiver.inclusion_star_injective/inclusion_pathStar_injective/pathInclusion_faithful`
は元の有限頂点の包含による生成辺と全射列の忠実性。
`liftPath/liftPath_projection/liftArrow/liftArrow_projection/liftArrow_unique` は
内部の全頂点を含む元の射列の一意な持ち上げ。
`diagramPathSupport/diagramPathSupport_arrow/diagramPathSupport_vertex` と
`FiniteQuiver.liftFunctor/liftFunctor_projection` は元の有限図式の同じ全射列を回収する。
`zigzagPathSupport/gridPathSupport` は元の全横列・全縦射の内部頂点を集める。
`FiniteGrid.row/map/functor/row_projection/map_projection/functor_projection` は
同じ有限支持内の全 grid を元の同じ関手へ厳密に回収する。
`QuiverTree.endpointHull/endpointHull_closed/endpointHull_mono` は両端を含む根に閉じた有限包。
`FiniteGrid.hull/rootedFunctor/rootedFunctor_projection/rootedHammock_isWeaklyContractible`
は元の全有限 grid をそのような有限包へ因子化し、同じ包の可縮性へ接続する。
空語・元の有限図式・任意可換環の実際の全自由次数と全 hammock 次数でも検証。
有限部分集合の厳密な全図式・全語との整合・全被覆への filtered 余極限も完成。
`RootedFinite.graphColimitIso/graphColimitDiagramIso/hammockColimitIso` は
有限包の全語の余極限から元の全体の hammock を回収し、同じ全標準射を保持する。
`weakFiniteSubsetColimitMap/finiteSubsetColimit_isWeaklyContractible` は元の有限部分集合の
filtered 余極限へ各項の弱同値と弱可縮性を移す。
`RootedFinite.colimit_isWeaklyContractible` と
`FreeQuiverCover.colimit_isWeaklyContractible` は全被覆の元の全端点の hammock の弱可縮性。
`hammockValueFiber_isWeaklyContractible/existingHammockValueFiber_isWeaklyContractible` は
元の評価の各 fiber の弱可縮性。任意可換環の実際の全自由次数への代入も検証する。
左右の DK 比較射の弱同値性と Map^h の高次比較は引き続き未完成。
`ValueSupport.subcomplex/singletonFiberIso/diagram/colimitIso` は元の離散な値ごとの
部分複体を有限部分集合の余極限で回収し、元の全標準射と評価への自然性を保持する。
`finite_restriction_weak/weak_of_singleton_restrictions/weak_of_contractible_fibers`
は元の各値の制限・fiber から元の評価自身の弱同値性を導く。
`FreeQuiverCover.hammockValue_isWeakHomotopyEquivalence` と
`existingHammockValue_isWeakHomotopyEquivalence` は全指定自由圏の同じ評価の弱同値性。
`topEquivalence_colimitMap_weak` と `Zigzag.Value.colimitValue_relative` は
元の unit/counit と同じ評価を保持する圏同値の移送。
`AllMarked.nativeFreeEvaluation/nativeValue/nativeValue_isWeakHomotopyEquivalence`
は元の指定部分圏の実際の評価の弱同値性。任意可換環の全自由次数へも代入して検証。
両 DK 比較射の弱同値性と Map^h の高次比較は引き続き未完成。
`tensorHomotopy/weakTensor` は元の有限積の弱比較を、Kan 置換の単位の消去で与える。
`IndexedSum.space/singletonIso/map_weak` は任意の同じ添字の依存和の弱比較。
`MarkedSpine.products/productsMap_weak/sumProductsMap_weak/productsIso` は
元の全因子列を非指定生成列ごとの有限個の指定因子の積の和へ厳密に戻す。
`ValueSpine/valueProductsIso/evaluation_isWeakHomotopyEquivalence` と
`hammockEvaluation_isWeakHomotopyEquivalence` は元の全指定因子を自由 groupoid の値に
置き換えた離散な因子列への同じ全評価自身の弱同値性。
`ValueSpine.compose/compose_assoc/valueCategory/valueMarkedFunctor` は値の因子列の
局所選択する圏構造と指定自由 groupoid の包含。元の指定矢を実際に反転する。
通常の局所化 Hom との同定と両 DK 比較射の弱同値性は引き続き未完成。
`MarkedSpine.valueLift/valueLift_inverts` は元の自由圏から値の因子列への関手と
元の W.paths の反転。`markedValueDescent/valueFoldFunctor/valueDescent/valueDescent_fac`
は Core への元の指定生成矢の像を延長し、元の任意の反転関手を厳密に回収する。
`localizationToValue/valueToLocalization/valueLocalizationEquivalence` は元の通常の局所化との
厳密な両往復を持つ比較。`localizationHomEquiv/valueLocalizationHomIso` は
元の同じ Q の Hom と値の因子列の同型であり、元の両関手の射写像を順逆射にする。
`nativeFreeEvaluation_descent/nativeValue_localizationValue` は元の指定因子の評価を
同じ局所化評価へ回収する。任意可換環の全自由次数への代入も検証。
全因子列の評価と同じ局所化評価の一致、両 DK 比較射の弱同値性は引き続き未完成。
既存 DK Hom との比較は Dwyer–Kan 命題2.2の二つの比較を構成して検証する必要がある。
相対関手による写像の構成だけで比較の弱同値性を完成としない。
既存 DK Hom の自由解像との高次の照合と ∞ 局所化の普遍性は後続。
添字圏・graph は [Dwyer–Kan 1980b §4–5](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-2.pdf)
を参照。Π は一般に filtered ではなく、その性質を余極限の証明に仮定しない。
比較の構成は [Low, §3.2〜3.7](https://arxiv.org/pdf/1409.8062)（Dwyer–Kan §7 の整理）を参照。
DK と既存 Map^h の高次の単体集合の比較・∞ 局所化の普遍性、
忘却先と既存 D(R) との比較、離散対象の ∞ 関手と離散性・極限保存・G1′ は未完成。

原典：
[Berger–Moerdijk 2003](https://arxiv.org/pdf/math/0206094)、
[Berger–Fresse 2004](https://arxiv.org/pdf/math/0109158)。
