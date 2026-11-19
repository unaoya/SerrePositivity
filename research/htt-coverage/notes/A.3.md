# HTT §A.3

<!-- NB-W3 (b) からの転記 -->

## 05-gamma-bridges.html — 4. γ4：Quillen 随伴 ⇒ ∞ 随伴

<!-- source: exposition/ja/infinity/05-gamma-bridges.html:86; block: nbw3-05-gamma-bridges-l86 -->
<a id="nbw3-05-gamma-bridges-l86"></a>

設定：simplicial モデル圏 \(\mathcal C,\mathcal D\)（SM7 を固定）と、豊穣 Hom の同型と合成の両立を明示した simplicial Quillen 随伴 \(F\dashv G\)。cofibrant かつ fibrant な対象（cf 対象）がなす単体的圏は SM7 により局所 Kan なので、γ1 によりその coherent nerve \(N^{hc}(\mathcal C^{cf})\) は quasicategory になる。

<!-- source: exposition/ja/infinity/05-gamma-bridges.html:87; block: nbw3-05-gamma-bridges-l87 -->
<a id="nbw3-05-gamma-bridges-l87"></a>

```text
lemma quillenCfDerivedAdjunction_exists :
    ∃ H : SSet.Homotopy (𝟙 (SimplicialNerve (CofibrantFibrantObjects C)))
      (quillenCfLeftDerived R adj fibD e SC SD ≫ quillenCfRightDerived R adj SC SD cofC),
      ∃ a : QCatAdjunction (quillenCfLeftDerived ...) (quillenCfRightDerived ...),
        a.unitHom = SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)
```

<!-- source: exposition/ja/infinity/05-gamma-bridges.html:92; block: nbw3-05-gamma-bridges-l92 -->
<a id="nbw3-05-gamma-bridges-l92"></a>

場所：HomotopyLimits/QuillenCfDerivedAdjunction。導来関手 \(\mathbb LF\)、\(\mathbb RG\) が cf nerve の間の ∞ 随伴（第 4 章の `QCatAdjunction`）をなし、その単位は指定したホモトピーから来る。系として、右導来関手は ∞ 極限を保つ（`quillenCfRightDerived_hasLimit_postcomp`、HomotopyLimits/QuillenCfDerivedLimits。一般の「右随伴は極限を保つ」`hasLimit_postcomp_of_adjunction` の適用）。

<!-- source: exposition/ja/infinity/05-gamma-bridges.html:93; block: nbw3-05-gamma-bridges-l93 -->
<a id="nbw3-05-gamma-bridges-l93"></a>

**証明の方針**（HTT 5.2.4.6）：\(\Delta^1\) 上の「cf 対応圏」を作る。両端の fiber が \(\mathcal C^{cf}\) と \(\mathcal D^{cf}\) で、二つをつなぐ混合 Hom は \(\mathrm{Map}(FX,Y)\cong\mathrm{Map}(X,GY)\) である。その coherent nerve \(\to\Delta^1\) が cocartesian かつ cartesian な fibration であることを示し（HomotopyLimits/QuillenCfBifibration）、cocartesian 辺に沿った transport と cartesian 辺に沿った transport を導来関手と比較する。そのうえで、写像空間の同値から随伴を組み立てる（Quillen*、34 ファイル）。
