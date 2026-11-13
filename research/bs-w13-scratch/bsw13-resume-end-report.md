
### C1′ の底変換の残り

`completeBaseChangeH0` を既存の有界上側の底変換と同じ自由解像度で比較し、基底環の零次単位同型 `completeBaseChangeUnitIso` を得た。古典的な商の完備底変換を零次の `(R′/JR′)_perfd` と比較する `quotientBaseChangeDerivedIso` も得た。両者は `/tmp/bsw13-basechange-coefficients.lean` で型検査・公理検査済み（標準三公理）。

残る `perfectoidIdeal_baseChange` は、完備底変換した短完全列の零次の長完全列で核を同定する。指定射の像まで含めた候補は `/tmp/bsw13-basechange-probe.lean` にある。候補全体の検査は約 5 分で打ち切って共有鍵を解放したため、型検査済みなのは上記の二つの比較まで。正規化した射 `R′ → (R′/JR′)_perfd` の全射性が得られれば、標準商写像と同じ核を持つ。任意の完備複体での反映には、さらに完備底変換とテンソルの比較、および完備忠実平坦な底変換での零性の反映を接続する必要がある。

Prop 10.4 と Lemma 10.5 の係数三角形は共通化した。最新の対象監査も 186 宣言、標準三公理のみ。C2 の既存宣言は再利用できる。この段の登録候補は上記の五モジュール。C1′ の底変換による反映は drafts に残し、ここまでを段 1 の報告とする。
