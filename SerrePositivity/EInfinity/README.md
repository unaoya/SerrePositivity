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
融合後の実際の行列と経路の元の置換頂点列の全体の一致は未完成。
候補経路上の置換合成の table reduction の成功・合成語との一致・一意性、
TR の一般の合成保存・微分との両立・オペラッド公理は未完成。
具体的な Δ¹ の余代数構造とその代入、E2a-4・5、E2b・G1′ は未完成。

原典：
[Berger–Moerdijk 2003](https://arxiv.org/pdf/math/0206094)、
[Berger–Fresse 2004](https://arxiv.org/pdf/math/0109158)。
