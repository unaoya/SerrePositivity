# 次の法則：有限 Koszul と係数テンソルの自然性

未実装の証明案。HT02 の外の範囲は追加しない。

1. `koszulCochainTensorIso x K` の K に関する自然性を有限列の長さで帰納する。
   - 空列：`cochainTensorLeftUnitor` の自然性。
   - 後続：`cochainTensorConeLeft_naturality_right`、写像錐の射を同じスカラー射に変える等式からの同型、帰納仮定。
   - 錐の射の等式の比較は一般の φK=smulId a K、φM=smulId a M の補題に切り出し、subst して Arrow の二つの成分と proof irrelevance で確認する。
2. `scalarConeKoszulIso a x K` の自然性を、1 と `cochainTensorUnitScalarConeIso_naturality`、結合・対称性の自然性から得る。
3. `Koszul x` は、x の末尾の元についての標準完備化単位を擬同型へ送る。
   末尾のスカラー錐を残りの Koszul と交換し、元の `complexCompletionUnit_koszul_quasiIso` の n=1 を使う。
4. `finiteCompletionUnit x K` の Koszul 簡約が擬同型であることを列の長さで帰納する。
   内側の単位の簡約には残る末尾の scalarConeFunctor の擬同型保存を使い、外側の単位には3を使う。
5. 全座標の完備性と `homology_isZero_of_finitelyComplete_koszul` を使い、
   元の有限 Koszul 下界と同じ b で `finiteCompletionFunctor x` の値の下界を得る。
   列長を再び差し引かない。

元の主元完備化と合成単位を反復する。別の完備化模型・任意の射・追加の Tor 仮定へ置き換えない。
