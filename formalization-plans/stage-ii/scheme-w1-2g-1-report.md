# SC-W1 2g-1：幾何の供給の実装記録

2026-11-14。承認された Rydh 3.10 経路。外枠 **25,000 行**、約 **12,000 行**で止まらず途中報告。G1・G2 の完成後に停止点 2g-1 を報告し、G3 へ進む。このファイルは現時点では途中記録で、完成報告ではない。main は凍結中、自分の枝 math/scheme だけで作業する。

## G1 の最初の束：型つき一覧（着手前）

G0 の環とスキームの付値判定から、Rydh の subtrusive な持ち上げへ進む。最初は次の型に絞る。

1. `exists_valuation_specialization_diagram`：Y は任意のスキーム、p⤳q は点の特殊化。κ(p) の付値部分環 W と k:Spec W→Y が存在し、k は閉点を q へ送り、Spec κ(p)→Spec W→Y は p の標準剰余体射と一致する。
2. `IsSchemeVCover.liftsSpecializations`：f:X→Y が G0 の IsSchemeVCover を満たすとき、p⤳q に対し x⤳z、f(x)=p、f(z)=q となる x,z が存在する。特定の x を固定した generalizing/specializing map の性質とは区別する。

1 は Mathlib の stalkSpecializes、局所環から体への射の付値部分環による因子化、fromSpecStalk の既存の法則を使う。2 は 1 の付値環へ G0 の付値持ち上げを適用し、忠実平坦拡大の閉点と一般点を取る。式の分割・自然性・Spec の係数移送は本数で区切らず、型をここへ追記する。200 行を超えた宣言・証明分割は行数を記録する。

この束は Rydh 3.10 の完成ではない。非 proper な有限表示射の strict transform の平坦化、付値判定から strict transform の全射性への接続、非 Noether affine 基底の模型は引き続き必要。
