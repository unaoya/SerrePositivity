# BS-M15（⑤d）作業報告

## 1. 着手・M15 段0（2026-11-14、紙）

指定 worktree `SerrePositivity-bs-m15`、枝 `math/bs-m15` で実施。
`git merge main` は `602fe450f → ac3544c4a` の fast-forward で完了した。
main には書き込んでいない。作業前の枝は clean。
指示書 `bhatt-scholze-codex-m15.md` §1–4 を読んだ。
⑤a の `../SerrePositivity-bs-impl/formalization-plans/bhatt-scholze/report-codex-w16.md`
§60–61・§66・§95・§97・§107・§111 を読み取り専用で引き継いだ
（同 worktree の HEAD は `e95184dc1`）。⑤a の未コミット分も含む作業木を変更していない。

**段0判定：追加 Lean の見込みは 7,000〜11,700 行。上端が事前承認の
8,500 行を超えるため、指示書 §3.1 に従って実装前に停止する。**
以下は残る数学的出力の型案で、Lean に追加した宣言でも型検査済みコードでもない。
未供給の構成を仮定の束へ移して完成とする案は採用しない。

### 1.1 再利用の確定範囲と見積もりの変更理由

既存ソースで次を照合した。

- `DGAlgebraDerivedInfinity.lean` の `dgAlgebraDerivedInfinityCategory` と安定性は
  `Mon (Complex A)` 上の**右**加群を扱う。一般 R を H⁰(R) に置き換える必要はない。
- `DGAlgebraMoritaInfinity.lean` の
  `dgAlgebraExtensionInfinity_isQCatEquivalence_of_quasiIso` は同じ dg 代数射の
  準同型から拡大の同値を供給する。この証明を作り直す費用は除いた。
- `DGModuleDerivedFunctor.lean` の `dgModuleDerivedFunctor` は射影的対象の保存を要求する。
  任意の係数射の restriction はその仮定を満たすとは限らない。
  restriction 後の解像度を含む全関手と、native な随伴の単位・余単位は依然必要。
- `HomologyComposition.lean` の `coefficientOperation_comp` は再利用できる。
  `HomologyAssociativity.lean` のホモトピー結合則から、同じ複体上の厳密な
  `Mon` の結合則は得たと数えない。標準零単体の全挿入（零 arity 込み）が最初の出力。
- `research/ha-coverage/review/ch4.csv` は HA 4.2.1.15・4.2.3.5・4.5.2.1 を
  通常圏に限る部分一致、4.5.3.1 を未供給と記録する。
  通常の balanced tensor は native な対称相対テンソルの構成済み API ではない。
- `drafts/DerivedGeneral/CompletionFunctor.lean` の `completionReflection` と
  `cAlgCompletionReflection` は `sorry` のまま。これらを証明済みの反射として
  無償に取り込まず、M15 に必要な module 完備反射と比較を費用へ入れる。
  A5 の Koszul・Nakayama の個別証明まで M15 に移す見積もりではない。

§95・§107 の 2,500〜4,500 行は暫定値だった。今回は次の全出力を一覧に含めた上で
束を再評価した。既存 dg nerve・安定性・拡大の弱同値不変性は再実装しない。

| 束 | 下端 | 上端 | 型一覧 |
| --- | ---: | ---: | --- |
| 同じ台の厳密忘却、固定模型の台・単位・指定辺 | 900 | 1,600 | M01–M05 |
| native restriction・随伴、恒等・合成と全族の降下 | 1,000 | 1,800 | M06–M10 |
| E∞ 相対テンソルの全構造・底変換 | 1,800 | 2,800 | M11–M15 |
| fiber・指数射、単位底比較と thick の共通化 | 600 | 1,000 | M16–M20 |
| 指数判定・底変換・合成・テンソル | 900 | 1,500 | M21–M27 |
| Amitsur 塔と指定増大の降下 | 600 | 1,000 | M28–M30 |
| RHom の係数付き全関手・評価と指数二の判定 | 500 | 800 | M31–M35 |
| 完備加群・完備テンソル・余極限評価・利用側接続 | 700 | 1,200 | M36–M42、離散特殊化 |
| **計** | **7,000** | **11,700** | |

前の三分割では「一般 R 加群」2,500〜4,500 が **4,300〜7,200**、
「指数」900〜1,500 は不変、「降下・評価・完備」1,400〜2,500 が **1,800〜3,000**。
差分は計 **+2,200〜+3,200**。全族の降下・随伴・対称テンソルと、
未証明の完備反射を独立に検収できる出力として積んだことによる。
これは実装前の工数見積もりで、必要行数の数学的下界ではない。
外枠二倍を使って事前承認の判定を回避しない。

### 1.2 型一覧の読み方・一般 E の境界

以下の記号は紙上の略記。未定義の名前の実在や型検査の成功を主張しない。

```lean
universe u
-- E : EInfinityTheory.{u}; A : Type u; [CommRing A]
-- Alg := E.CAlg A
-- V (C : SSet.{u+1}) := C _⦋0⦌
-- D := derivedInfinityCategory A
-- R B C : V Alg; f : SSet.Edge R B
-- C_R := modulesOver E A R; U_R := modulesOverForget E A R
-- one_R := moduleUnit E A R; B_f := algebraAsModule E A f
-- eta_f := algebraModuleUnit E A f : SSet.Edge one_R B_f
-- T_R M := moduleTensorWith E A R M : C_R ⟶ C_R
-- Ext f := moduleExtend E A f; Res f := moduleRestrict E A f
-- hC := C.HomotopyCategory; [e] := homMk e.toTruncated
-- DLE k X := ∀ i : ℤ, k < i → Subsingleton (derivedInfinityHomology A i X)
```

全族とは、実 cocartesian fibration `p : TotalModules ⟶ Alg` と、その R 上の fiber、
cocartesian transport としての `Ext f` をいう。M10 はこの実対象を構成する出力。
対称テンソルの全構造は有限基点集合上の実 operadic fibration として構成し、
単に hC_R の対称モノイダル圏だけを作って済ませない。
以下の `ModuleFamily`・`SymmetricModuleTensor` はその**数学的対象の型の仮名**であり、
未証明命題だけを欄にする Setup 型を追加する承認ではない。

注意：`EInfinityTheory` の任意の E には、BE 模型への比較や module の族の欄がない。
BE の `assocForget` だけを構成しても、任意の E に対する `modulesOver E A R` は得られない。
M10 はまず BE 模型で構成し、任意 E の入口を保つ場合は同じ CAlg・忘却との比較から
輸送できることを別途示す必要がある。現界面からその比較が導けるとは未確認。
ここは**未解決の型の境界**として明記し、E を無断で BE に特殊化しない。
上表は BE での構成と、利用側が同じ模型を参照する接続の見込み。
任意 E の表現定理を新たに証明する費用まで有限上端で保証するものではない。
この不確定性も、旧上端 8,500 を据え置いて実装開始できない理由である。

### 1.3 最初の受け渡し：M01–M20

原典番号の対応は⑤a §61.4・§95.3 のものを引き継ぐ。
HA 4.2.1.15、4.2.3.5・4.2.3.7、4.5.1.1・4.5.2.1・4.5.3.1。
番号の対応は、その一般定理が本リポジトリに実装済みであることを意味しない。
M01–M05 は BE 側の新設 `EInfinity/BarrattEccles/Modules/`、
一般の構成は `EInfinity/Modules/` に置く。既存のファイルは編集しない。

```lean
-- M01 標準零単体の係数（A・operad の引数は明示）
standardCoefficient (A : Type u) [CommRing A] (n : ℕ) :
  𝟙_ (Complex A) ⟶ (operad A).arity n
-- M02 単位（operad の単位）
standardCoefficient A 1 = (operad A).unit
-- M03 全挿入。n = 0 を除外しない
∀ (m n : ℕ) (i : Fin (m + 1)),
  coefficientComposite m n i (standardCoefficient A (m+1))
    (standardCoefficient A n) = standardCoefficient A (m+n)
-- M04 同じ carrier・元の複体の単位と積・全代数射を持つ忘却
assocForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)
-- M05 固定模型の右加群、台の忘却と正則加群
strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1}
strictModuleUnderlying (X : (operad A).Algebra) :
  strictModuleInfinity A X ⟶ derivedInfinityCategory A
strictModuleUnit (X : (operad A).Algebra) : V (strictModuleInfinity A X)
-- C01（照合一）M04–M05 の台・正則加群・指定単位射と BE carrier の比較。
-- carrier は M04 で変えない。U(strictModuleUnit X) は同じ X.carrier の像。

-- M06 全厳密射の native 拡大・制限（g : X ⟶ Y）
strictExtend g : strictModuleInfinity A X ⟶ strictModuleInfinity A Y
strictRestrict g : strictModuleInfinity A Y ⟶ strictModuleInfinity A X
-- M07 通常圏の随伴の写しと同じ全単位・余単位を持つ native 随伴
QCatAdjunction (strictExtend g) (strictRestrict g)
-- M08 恒等・合成（拡大。restriction は逆順）
FunctorIso (strictExtend (𝟙 X)) (𝟙 _)
FunctorIso (strictExtend (g ≫ h)) (strictExtend g ≫ strictExtend h)
-- M09 同じ拡大の弱同値不変性
QuasiIso g.hom → IsQCatEquivalence (strictExtend g)
-- M10 全族・native な辺と合成への降下。上の transport を含む実構成
moduleFamily A : ModuleFamily (barrattEcclesCore.CAlg A)
-- fiber が C_R、transport が Ext f。高次単体も含む射影を構成する。
-- C02（照合二）厳密族の局所化との全関手比較、同じ U・単位・随伴。

-- M11 同じ C_R に対する相対テンソルの operadic 構造
moduleTensorStructure A R : SymmetricModuleTensor C_R
-- M12 同じ単位と左右単位子（全関手同型）
FunctorIso (T_R one_R) (𝟙 C_R)
-- M13 結合子・対称性は M11 の実 operadic 構造からの指定比較。
-- 頂点 M,N,P での表示：
VertexIso (tensor R (tensor R M N) P) (tensor R M (tensor R N P))
VertexIso (tensor R M N) (tensor R N M)
-- M14 両変数での完全性（M11 の対称性で第二変数へ）
∀ M : V C_R, IsExactFunctor (T_R M)
-- M15 拡大は対称モノイダル、同じ pushout に対する底変換
-- Q は CAlg の同じ正方形、f : R→B、g : R→R'、g' : B→B'、f' : R'→B'
IsColimitCone (pushoutCocone Q) →
  FunctorIso (Res f ≫ Ext g) (Ext g' ≫ Res f')
-- Ext f(one_R) ≃ one_B、Ext f(M⊗_R N) ≃ Ext f M⊗_B Ext f N は
-- 対称モノイダル関手という実構造に含める。合成・単位との coherence も要る。

-- M16 指定単位辺・fiber。fiberArrow f : F_f → one_R は実 fiber 錐の脚
algebraModuleUnit f : SSet.Edge one_R B_f
moduleFiber f : V C_R
moduleFiberArrow f : SSet.Edge (moduleFiber f) one_R
-- M17 反復相対テンソルと、同じ脚からの指定指数射
fiberPower f (n : ℕ) : V C_R
fiberPowerArrow f (n : ℕ) : SSet.Edge (fiberPower f n) one_R
-- n=0 は one_R の恒等射。全 n で F_f の脚のテンソルと単位子から作る。
-- M18 単位底での全関手比較（tensor・指定辺も含める）
moduleAtUnitEquivalence A : QCatEquivalence (modulesOver E A (unitAlgebra E A)) D
-- M19 thick の共通定義と tensor による閉性（1.6 を参照）
IsThickTensorIdeal (R : V Alg) (P : V C_R → Prop) : Prop
thickTensorIdealGenerated (R : V Alg) (M : V C_R) : V C_R → Prop
-- M20 定義二つ。相互同値を定義に埋め込まない
IsDescendableOver A R B f := thickTensorIdealGenerated R B_f one_R
HasDescentIndexLEOver A R B f n := ([fiberPowerArrow f n] = 0)
-- C03（照合三）同じ E.forget が送る f と M16–M18 の台・fiber・指数射の比較。
```

M01–M20 が⑤a §107.3 の五点を全て満たして初めて最初の受け渡しとなる。
M08 の二つの同型を孤立して作るだけでは M10 の高次の降下を満たさない。
M13 の頂点同型だけでも M11 を満たさない。C01–C03 は補助照合の予定上限三本。
本一覧の主出力を細分して本数を増やす数え方はしない。

### 1.4 指数・降下：M21–M30

略記 `Desc f`・`Idx f n` は M20 の二つの Prop。
`bottom Q` 等は drafts と同じ `squareBottomArrow` 等から `.ofTruncated` で戻した辺。
`Arrow := (ihom Δ[1]).obj Alg`、`edge v` は drafts の `algebraArrowEdge`。

```lean
-- M21 Mathew Definition 3.18 の定義からの有限指数判定
Desc f ↔ ∃ n : ℕ, Idx f n
-- M22 単位底特殊化（Shared の離散定義との一致）
Desc (f : SSet.Edge (unitAlgebra E A) B) ↔ IsDescendable E A B
-- M23 底変換
IsColimitCone (pushoutCocone Q) → Desc (bottom Q) → Desc (top Q)
-- M24 同じ正方形での指数保存
IsColimitCone (pushoutCocone Q) → Idx (bottom Q) n → Idx (top Q) n
-- M25 指定合成の証人を保持
SSet.Edge.CompStruct f g h → Desc f → Desc g → Desc h
-- M26 相対テンソル（同じ pushout の対角辺）
IsColimitCone (pushoutCocone Q) →
  Desc (bottom Q) → Desc (left Q) → Desc (diagonal Q)
-- M27 始域も異なる二辺のテンソル。D₂ は Fin 2 の離散図式
(c : JoinCocone D₂) → IsColimitCone c →
  (∀ j : Fin 2, Desc (edge (D₂.app _ (ULift.up (nerveVertex (Discrete.mk j)))))) →
  Desc (edge c.vertex)
-- M28 任意の R 加群への Amitsur 図式（実際の増大・全脚を保持）
moduleAmitsur (d : AmitsurData E A f) (M : V C_R) :
  augmentedShape ⟶ C_R
-- M29 指数の零性から同じ module 増大錐の極限性
Idx f n → IsLimitCone (moduleAmitsurAug d M)
-- M30 Shared の要求する CAlg の同じ増大錐（M=one_R）
Desc f → (d : AmitsurData E A f) → IsLimitCone d.aug
```

M29 では Amitsur の部分 Tot の塔と fiber のテンソル冪の関係から収束を証明する。
有限段の retract が得られたことだけを無限 Tot の極限性と読み替えない。
M30 の `AmitsurData` の base・zero・leg・term は既存 drafts のものを使い、
都合のよい別の増大へ差し替えない。Mathew Proposition 3.22 の利用箇所。

### 1.5 RHom・完備版・A5 の入力：M31–M42

```lean
-- M31 R 加群の内部 Hom と、その台を取る全関手
moduleRHom R : C_Rᵒᵖ ⊗ C_R ⟶ C_R
-- ここで C_Rᵒᵖ は simplicial opposite。⊗ は SSet の積。
-- M32 同じ tensor と内部 Hom の随伴（任意の M）
QCatAdjunction (T_R M) (moduleRHomWith R M)
-- M33 評価の h 上の零次比較（相手 N を動かす自然な加法同型）
((hC_R).Hom M N) ≃+
  derivedInfinityHomology A 0 (U_R (moduleRHomObj R M N))
-- M34 A 係数付き Hom。L は任意の D(A) 頂点、平坦性を要求しない
fiberSquareRHom (f : SSet.Edge R B) (L : V D) : V D :=
  U_R (moduleRHomObj R (fiberPower f 2) (moduleFromBase R L))
-- moduleFromBase R は R⊗_A(-) の実 ∞ 関手。tensorWith の向きを固定する。
-- M35 Shared の True を置き換える実質的主張
DLE (-1) (fiberSquareRHom f (unitComplex A)) → Idx f 2

-- M36 台が s 完備な R 加群の充満部分準圏と反射
completeModules R (s : Finset A) : SSet.{u+1}
moduleCompletion R s : C_R ⟶ completeModules R s
QCatAdjunction (moduleCompletion R s) (completeModulesInclusion R s)
-- M37 完備テンソルと単位。通常の tensor の後の完備化
completeTensor R s M N := moduleCompletion R s (tensor R M.val N.val)
-- 完備 R のとき単位は one_R、M11 と同じ向きの対称 operadic 構造を構成。
-- M38 完備圏での定義と指数判定（通常版との同値を定義にしない）
IsDescendableCompleteOver A s R B f : Prop
HasDescentIndexLECompleteOver A s R B f n : Prop
IsDescendableCompleteOver A s R B f ↔
  ∃ n, HasDescentIndexLECompleteOver A s R B f n
-- M39 Shared の完備版 True の代わり。cR,cB は忘却した台の完備性
(cR : IsDerivedComplete A s ((E.forget A).app _ R)) →
(cB : IsDerivedComplete A s ((E.forget A).app _ B)) →
  Desc f → IsDescendableCompleteOver A s R B f
-- 指数 n も同じ仮定で保つ。逆向きは要求しない。
-- M40 BS17 Lemma 11.22 の Shared での入口（Dseq は Arrow の ℕ 図式）
(c : JoinCocone Dseq) → IsColimitCone c →
  (∀ j : ℕ, Idx (edge (Dseq.app _ (ULift.up (nerveVertex j)))) n) →
  Idx (edge c.vertex) (2*n)
-- M41 完備圏での同じ余極限評価（complete Arrow の中で hc を要求）
(c : JoinCocone DseqComp) → IsColimitCone c →
  (∀ j : ℕ, HasDescentIndexLECompleteOver A s _ _ (edgeComp (DseqComp.app _
    (ULift.up (nerveVertex j)))) n) →
  HasDescentIndexLECompleteOver A s _ _ (edgeComp c.vertex) (2*n)
-- M42 完備版 Amitsur の同じ増大錐についての降下
IsDescendableCompleteOver A s R B f →
  (d : CompleteAmitsurData A s f) → IsLimitCone d.aug
```

`U_R (...)` 等の頂点適用は `app (op ⦋0⦌)` の略記。
M33 の `M N` は hC_R の対応頂点、左辺は加法的 Hom 群とする。
M35 の `unitComplex A` は D(A) の A。DLE は drafts の
`Derived.IsConnectiveAt A (-1)` と同じ条件（H^i=0、i>−1）であり、符号を反転しない。
M31 は既存の空間値 Hom から内部 Hom の表現対象を供給する工程を含む。

A5/StrongDescent の `fiberSquareRHom`（97 行）の入力型と M34 を一致させる。
特に **RHom_R(F⊗_R F, R⊗_A L)** を使い、
`RHom_R(F⊗_R F,R) ⊗_A L` を任意の L に対して同一視しない。
A5 の Koszul 接続に要るのは M32 の底変換随伴と、**双対可能な K に限る**
次の射の同値性：

```lean
IsDualizable K → Nonempty (VertexIso
  (fiberSquareRHom f K)
  ((tensorWith K).app _ (fiberSquareRHom f (unitComplex A))))
```

これは M32・M34 の係数作用の投影公式として証明する主出力の一部。
A5 の任意離散係数での負次数評価、Koszul 塔の最高次全射、Nakayama は A5 のまま。
RHom の負次数性を M15 の仮定として束ねて A5 の証明済み結果にはしない。

完備 R,B のもとで A5 が必要とする結論は完備圏の descendability。
現 `StrongDescent.lean` は完備版の説明で非完備版 `IsDescendableOver` を表示しているため、
M39 だけではその表示どおりの通常版を逆に導けない。完備版 Prop を A5 が使うのか、
通常版まで別途証明するのかは型の受け渡し時の確認点とする。drafts は無断修正しない。
完備版だけを証明して通常版の完成とは報告しない。

Shared の離散版 `HasDescentIndexLE`、指数判定、baseChange・comp・tensor・Tot、
Frobenius の `DiscreteSource` 付き版、`IsDescendableComplete` への特殊化は
M18・M22・M24–M30・M39–M40 から元の全引数のまま供給する互換出力。
型は `drafts/Shared/Descendable.lean` の同名宣言と同一に保つ。
同ファイル末尾の `isDescendable_of_faithfullyFlat`（Mathew Prop 3.31）は A5 が使わない
別の数学的結果で、上記 M15 引き継ぎの指数・降下・完備版の実装済み数には含めない。

### 1.6 K の R53 との共通化

`refactor-ledger.md` の R53 の行は現版では **55 行（§8 より前）**にある。
「K の再開の①の段0で扱う」という計画状態。
本体全体を `rg` で検索したところ、単語としての `IsThick`・`thickClosure` は未発見。
`StableHoGeneration.lean` は docstring でも明示的に retract 閉包を含めない。
これをそのまま thick と呼ぶことはできない。

一本化案：安定準圏 C 上の頂点述語 P に対する `IsThick C P` を共通の芯とし、
同型・零対象・実 cofiber/fiber・retract で閉じる条件を置く。
`IsThickTensorIdeal` はそれに `∀ x M, P x → P (T M x)` を加えるだけとする。
shift と有限余極限の条件との同値を証明し、drafts の定義へ接続する。

```lean
-- 芯と tensor の閉性の分離（紙上の型）
IsThickTensorIdeal R P ↔
  IsThick C_R P ∧ (∀ x M : V C_R, P x → P ((T_R M).app _ x))
-- 定義の交わりによる生成の普遍性
thickTensorIdealGenerated R M N ↔
  ∀ P : V C_R → Prop, IsThickTensorIdeal R P → P M → P N
```

数学的な共通化は可能だが、既存の K の完成 API に import を差すだけでは済まない。
新しい汎用 `IsThick` を `EInfinity/Modules/` に置いて K から EInfinity へ依存させるのも
不適切なので、K の①での共通配置と公開名を調整すべき境界として記録する。
今回は R53 の実装や台帳の状態を先取りせず、M19 の費用内に比較を確保した。

### 1.7 実測・検証・停止

- 追加はこの報告書一本。Lean ファイル **0 本・0 行・0 宣言**、証明完了 **0 本**。
- M01–M42 は紙の主出力の識別子。恒等・合成や operadic 構造内の法則を含むため、
  「42 個の Lean 定理を証明した」という実測ではない。
- 各主出力に対する前提計算は三本まで、補助照合は C01–C03 の三本までという規則を
  維持する。一覧外の新しい数学が判明した場合は追加枠として進まず報告する。
- 対象ビルド・公理監査は未実施。Lean の変更がなく、段0の上端超過で実装前に
  停止したため。共有ビルド鍵・整理券は取得していない。大きい監査も行っていない。
- 小さい監査は `git diff --check` と変更パスの確認。⑤a 所有の既存ファイル、
  `EInfinity/Interface/`、drafts、main は変更しない。
- M15・G12 の停止点1・2には未到達。上限超過による段0停止を G12 着手で迂回しない。

再開時の判断材料は (i) 上端 11,700 の扱い、(ii) 一般 E の入口と BE への輸送の型、
(iii) A5 の完備版 Prop の受け渡し。これらを未証明の新 interface 欄や仮定にして
隠さず、段0の報告として自分の枝に保存する。


## 2. D80 承認後：標準係数・結合的忘却・厳密底の加群関手（11-14）

ユーザーの段0承認と指示書 §5 を受領。外枠は **17,000 行**、約8,500行での
途中報告を維持する。任意 E への輸送は作らず、BE 模型と A5 の特殊化で進める。
main の承認文書（`41101afb1` を含む）を自分の枝へマージした。
main 自身・⑤a の所有する既存ファイル・界面には書き込んでいない。

### 2.1 検証済みの新設三本

全て `SerrePositivity/EInfinity/BarrattEccles/Modules/` 配下。

| ファイル | 行数（空行・docstring 込み） | 明示宣言数 | 出力 |
| --- | ---: | ---: | --- |
| `StandardCoefficient.lean` | 129 | 9 | M01–M03：全 arity の標準零単体、単位との一致、厳密な全挿入 |
| `AssociativeForget.lean` | 183 | 12 | M04：同じ carrier の結合的 dg 代数と全代数射の忘却関手 |
| `StrictModules.lean` | 108 | 9 | M05 の実構成、M06 の二関手、M09 の拡大の弱同値不変性 |
| **合計** | **420** | **30** | |

生成された補助宣言を含まない明示 `def/abbrev/lemma/theorem` の実測。
M01–M04 は検証済み。M05 は台・正則加群の実頂点を構成したが、
解像度後の台と元の正則加群の指定比較（C01 の残り）は未完。
M06 は全厳密射の拡大・制限の実 ∞ 関手を構成済みで、M07 の随伴はまだ別工程。
M09 は同じ拡大の弱同値不変性が検証済み。
M08・M10 以降の全族・相対テンソル・指数・降下・RHom・完備版は未完。
**固定した厳密底の段階を、native CAlg の全辺への降下の完成とは数えない。**

### 2.2 実装の内容と残る受け渡し

M03 は収縮の切断を使わず、各 arity の恒等置換の零単体から作った。
shuffle 次数 `(0,0)` の経路は一意で符号は一、内側・外側の恒等置換の合成も恒等。
これを元の複体の零次の一の像で検査し、`n=0` 込みで厳密な合成則を証明した。
M04 の左右単位則・結合則はこの等式と代数の作用公理から得た。
右単位則に可換性やホモロジー上の一致は使っていない。
原典対応は Berger–Fresse §1.1.1–1.1.3。

主出力の型は段0どおり。実名は以下。

```lean
standardCoefficient_composite (A : Type u) [CommRing A]
    (m n : ℕ) (i : Fin (m+1)) :
  coefficientComposite m n i (standardCoefficient A (m+1))
    (standardCoefficient A n) = standardCoefficient A (m+n)
assocForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)
assocForget_forget (A : Type u) [CommRing A] :
  assocForget A ⋙ Mon.forget (Complex A) = Operad.Algebra.forget (operad A)
strictModuleUnderlying A X : strictModuleInfinity A X ⟶ derivedInfinityCategory A
strictModuleUnit A X : (strictModuleInfinity A X) _⦋0⦌
strictModuleExtend (f : X ⟶ Y) : strictModuleInfinity A X ⟶ strictModuleInfinity A Y
strictModuleRestrict (f : X ⟶ Y) : strictModuleInfinity A Y ⟶ strictModuleInfinity A X
strictModuleExtend_weak (f : X ⟶ Y) (hf : QuasiIso f.hom) :
  IsQCatEquivalence (strictModuleExtend f)
```

§1 の restriction の射影性保存の問題に対して、
`dgModuleDerivedFunctor` に仮定を足す経路は採用しなかった。
既存 `dgModuleResolvedInfinity` は任意の dg 加群値関手の出力を全関手的に解像する。
これを半自由加群の全包含の後の `dgModuleRestriction` に適用して、実 restriction を構成。
台の忘却にも `moduleEvaluationDG` と `ringConstantDG` の後に同じ構成を使い、
`semifreePointEquivalence` で既存 D(A) に戻す。
正則加群は同じ一対象 dg 圏の representable を解像して指定した。

この出力解像度の存在は M07 の同じ単位・余単位の検証を自動では供給しない。
一般 kernel の `dgKernelAdjunction` と graph 比較は再利用候補として確認済み。
これと今構成した restriction の全関手比較が次の検査対象。

数え方：M03 の shuffle 二補題は前提計算二本。
M04 の全 arity における一入力単位則・部分合成則・射保存則は前提計算三本。
三つのモノイド公理は M04 の構造構成の証明分割として数える。
`assocForget_forget` は C01 の厳密な台の部分。C02・C03 は未使用。
新しい一覧外の数学の補題を追加したとは数えていない。

### 2.3 対象ビルドと小さい監査

全呼び出しを `scripts/refactor/with_build_lock.sh --class impl --wait 3600 -- ...` で実行。
新設三本だけを `lake env lean -o <自分の .lake の出力> <対象>` で検証した。
既存 main の olean は自分の .lake 配下の参照リンクから読み、新規三本の出力だけを
自分の worktree に作った。main と⑤a の build 成果物は書き換えていない。

三本の対象ビルド成功。新規30宣言の `#print axioms` の小監査も成功し、
全て **`propext`・`Classical.choice`・`Quot.sound` のみ**。
`sorryAx`・追加公理なし。監査入力は `/tmp/m15-small-audit.lean`、
ログは `/tmp/m15-small-audit.log`。全体ビルド・大きい監査は回していない。
`git diff --check` と新設三本の禁止語（`sorry`・`axiom`・`admit`）検査も実施する。

これは 420 / 17,000 行時点の区切り記録で、規模による停止ではない。
M15 の停止点1には未到達。引き続き M05 の指定比較・M07 の随伴・M08 の合成へ進む。


## 3. 共通の厚い閉包と native な graph 随伴（11-14、区切り）

追加の三本も対象ビルドを完了した。

| ファイル（SerrePositivity/ 以下） | 行数 | 明示宣言数 |
| --- | ---: | ---: |
| `InfinityCategories/HA/StableInfinityCategories/Thick.lean` | 80 | 5 |
| `EInfinity/Modules/ThickTensorIdeal.lean` | 57 | 4 |
| `EInfinity/BarrattEccles/Modules/StrictAdjunction.lean` | 48 | 2 |
| **今回** | **185** | **11** |
| **累計（六本）** | **605** | **41** |

### 3.1 共通の芯（M19 の一般部分）

`IsThick` は stable な準圏の頂点述語に対し、零・同型・実 cofiber・実 fiber・
ホモトピー圏の retract に関する閉性を持つ。
`thickClosure` を全ての厚い上界の交わりで構成し、生成元の包含・閉性・最小性を証明。
安定圏一般のファイルは EInfinity に依存しない。
原典の対応節は HA §1.1.3、HTT §4.4.5。

`EInfinity/Modules/ThickTensorIdeal.lean` の `IsThickTensorIdeal` は共通の
`IsThick` を継承して、指定した tensorWith の閉性だけを加える。
`thickTensorIdealGenerated` の閉性と生成元の所属も証明した。
原典対応は Mathew Definition 3.18。
これらは M19 の閉包構成の部分証明であり、別の数学的前提を束ねたものではない。

この段階の tensorWith は明示引数であり、BE 相対テンソルの実装済み性は意味しない。
BE の全族への代入、drafts の有限余極限・shift 表示との比較は未完なので、
**M19 全体を完了にはしない**。K 側の既存ファイルは編集していない。

### 3.2 M07 の native な随伴と残る型

同じ厳密 BE 射の `dgAlgebraMap` の graph に、既存の `dgKernelAdjunction` を適用し、
`dgKernelDerivedInfinity_graphIso` と `qcatAdjunctionChangeLeft` で
**既に指定した strictModuleExtend** を左随伴とする実随伴を構成した。
実右随伴の名前は `strictModuleAdjointRestrict`。

この随伴は全関手圏での単位・余単位と両三角式を持つ。
一方、§2 の `strictModuleRestrict` は生の dg 制限を全関手的に解像したもの。
現時点で両者は別の実関手であり、以下の型の比較が未完：

```lean
FunctorIso (strictModuleAdjointRestrict f) (strictModuleRestrict f)
```

この比較と指定された通常の拡大・制限の単位・余単位の接続を証明してから、
M07 完了と数える。h 上の `dgKernelRightAdjoint_classicalIso` だけを、
この全関手同型として使用しない。これは M07／C02 の受け渡しの残りで、
新たな任意 E への輸送や界面欄の追加には進まない。

### 3.3 検証・キャッシュ・現在地

新規三本の対象ビルド成功、累計六本の全41明示宣言の `#print axioms` 小監査成功。
全て標準三公理のみ、`sorryAx` なし。Lean ソースにも `sorry`・`axiom`・`admit` なし。
全体ビルド・大きい監査は実施していない。

一般の安定圏の出力先を追加した際、キャッシュ参照ディレクトリの symlink を
辿って **今回新設した Thick の olean 三ファイルだけ**が main 側のキャッシュへ
出たことを確認した。自分が作った三ファイルを内容照合後に自分の worktree へ移し、
共有側の当該三ファイルを除いた。本体ソース・既存成果物は変更していない。
ビルド補助 `/tmp/m15-target-build.py` を修正し、出力先の各親ディレクトリを
自分の実ディレクトリへ分離した上で、出力先が自分の worktree 内に解決されることを
assert するようにした。累計六本の olean の実パスも自分の worktree 内と確認済み。

現在の一覧：M01–M04 完了、M05（台・単位の比較）途中、M06（二関手）構成済み、
M07（native な graph 随伴は構成済み、同じ restriction への比較）途中、
M08 未完、M09（拡大の弱同値不変性）検証済み、M19（共通の芯）先行分。
M10 以降の残り、RHom・完備反射・完備テンソル、A5 の BE 特殊化は未完。
外枠 17,000 行に対し 605 行。M15 の完成や規模の停止を宣言する区切りではない。

### 3.4 部分補題・構成の型の記録

IS-W2 §14 の証明分割の記録として、ここまでの新設六本の明示宣言の型を列挙する。
名前空間・open・宇宙・型クラスの文脈は各ソースと同じ。証明本体は含めない。
構造の欄は各ソースに記載し、ここでは構造の入口を示す。

`EInfinity/BarrattEccles/Modules/AssociativeForget.lean`：

```lean
def standardOperation (X : (operad A).Algebra) (n : ℕ) :
    power X.carrier n ⟶ X.carrier

def standardBinary (X : (operad A).Algebra) : X.carrier ⊗ X.carrier ⟶ X.carrier

lemma standardOperation_one (X : (operad A).Algebra) :
    standardOperation X 1 = (oneIso X.carrier).hom

lemma standardOperation_composite (X : (operad A).Algebra)
    (m n : ℕ) (i : Fin (m+1)) :
    standardOperation X (m+n) =
      (λ_ (power X.carrier (m+n))).inv ≫
      tensorInsertionAction X.carrier (𝟙_ (Complex A)) m n i
        ((λ_ (power X.carrier n)).hom ≫ standardOperation X n) ≫
      standardOperation X (m+1)

lemma standardBinary_assoc (X : (operad A).Algebra) :
    (standardBinary X ▷ X.carrier) ≫ standardBinary X =
      (α_ X.carrier X.carrier X.carrier).hom ≫
        (X.carrier ◁ standardBinary X) ≫ standardBinary X

lemma standardBinary_one_mul (X : (operad A).Algebra) :
    (standardOperation X 0 ▷ X.carrier) ≫ standardBinary X =
      (λ_ X.carrier).hom

lemma standardBinary_mul_one (X : (operad A).Algebra) :
    (X.carrier ◁ standardOperation X 0) ≫ standardBinary X =
      (ρ_ X.carrier).hom

lemma standardOperation_map {X Y : (operad A).Algebra} (f : X ⟶ Y) (n : ℕ) :
    standardOperation X n ≫ f.hom =
      TensorPowers.map f.hom n ≫ standardOperation Y n

def associativeAlgebra (X : (operad A).Algebra) : Mon (Complex A)

def associativeAlgebraMap {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    associativeAlgebra X ⟶ associativeAlgebra Y

def assocForget : (operad A).Algebra ⥤ Mon (Complex A)

lemma assocForget_forget : assocForget A ⋙ Mon.forget (Complex A) =
    Operad.Algebra.forget (operad A)

```

`EInfinity/BarrattEccles/Modules/StandardCoefficient.lean`：

```lean
def standardSimplex (n : ℕ) : (simplicial n) _⦋0⦌

lemma simplexEquiv_standardSimplex (n : ℕ) (k : Fin 1) :
    simplexEquiv n 0 (standardSimplex n) k = 1

def standardCoefficientCycle (n : ℕ) : complexCycles A (complex A n) 0

def standardCoefficient (n : ℕ) : 𝟙_ (Complex A) ⟶ (operad A).arity n

lemma standardCoefficient_unit : standardCoefficient A 1 = (operad A).unit

lemma standardCoefficient_zero_apply (n : ℕ) (a : A) :
    (standardCoefficient A n).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv a) =
    a • (complexXIso A n 0).inv (normalizedGenerator A n 0 (standardSimplex n))

lemma shuffleSimplex_standard (m n : ℕ) (i : Fin (m + 1)) (s : ShufflePath 0 0) :
    shuffleSimplex m n i s (standardSimplex (m+1)) (standardSimplex n) =
      standardSimplex (m+n)

lemma shuffleBilinear_standard (m n : ℕ) (i : Fin (m + 1)) :
    shuffleBilinear A m n i 0 0
      (normalizedGenerator A (m+1) 0 (standardSimplex (m+1)))
      (normalizedGenerator A n 0 (standardSimplex n)) =
      normalizedGenerator A (m+n) 0 (standardSimplex (m+n))

lemma standardCoefficient_composite (m n : ℕ) (i : Fin (m + 1)) :
    coefficientComposite m n i (standardCoefficient A (m+1))
      (standardCoefficient A n) = standardCoefficient A (m+n)

```

`EInfinity/BarrattEccles/Modules/StrictAdjunction.lean`：

```lean
def strictModuleAdjointRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A Y ⟶ strictModuleInfinity A X

def strictModuleGraphAdjunction {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    QCatAdjunction (strictModuleExtend f) (strictModuleAdjointRestrict f)

```

`EInfinity/BarrattEccles/Modules/StrictModules.lean`：

```lean
abbrev strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1}

theorem strictModuleInfinity_isStable (X : (operad A).Algebra) :
    SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (strictModuleInfinity A X)

def strictModuleUnderlyingDG (X : (operad A).Algebra) :
    DGFunctor A (SemifreeDGAlgebraModules A ((assocForget A).obj X))
      (RightModule A PUnit.{1})

def strictModuleUnderlying (X : (operad A).Algebra) :
    strictModuleInfinity A X ⟶ derivedInfinityCategory A

def strictModuleUnit (X : (operad A).Algebra) : (strictModuleInfinity A X) _⦋0⦌

def strictModuleExtend {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A X ⟶ strictModuleInfinity A Y

def strictModuleRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A Y ⟶ strictModuleInfinity A X

theorem strictModuleExtend_isExactFunctor {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
      (strictModuleExtend f)

theorem strictModuleExtend_weak {X Y : (operad A).Algebra} (f : X ⟶ Y)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (strictModuleExtend f)

```

`InfinityCategories/HA/StableInfinityCategories/Thick.lean`：

```lean
structure IsThick (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (P : C _⦋0⦌ → Prop) : Prop

def thickClosure (P : C _⦋0⦌ → Prop) : C _⦋0⦌ → Prop

lemma subset_thickClosure (P : C _⦋0⦌ → Prop) {x} (hx : P x) : thickClosure C P x

lemma thickClosure_isThick (P : C _⦋0⦌ → Prop) : IsThick C (thickClosure C P)

lemma thickClosure_le_iff (P Q : C _⦋0⦌ → Prop) (hQ : IsThick C Q) :
    (∀ x, thickClosure C P x → Q x) ↔ ∀ x, P x → Q x

```

`EInfinity/Modules/ThickTensorIdeal.lean`：

```lean
structure IsThickTensorIdeal (C : SSet.{u}) [Quasicategory C] [IsStable C]
    (tensorWith : C _⦋0⦌ → (C ⟶ C)) (P : C _⦋0⦌ → Prop) extends IsThick C P

def thickTensorIdealGenerated (M : C _⦋0⦌) : C _⦋0⦌ → Prop

lemma generated_isThickTensorIdeal (M : C _⦋0⦌) :
    IsThickTensorIdeal C tensorWith (thickTensorIdealGenerated C tensorWith M)

lemma mem_generated (M : C _⦋0⦌) : thickTensorIdealGenerated C tensorWith M M

```
