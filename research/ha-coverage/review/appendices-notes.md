# 付録A・Bの照合

2017-09-18版。付録Aは135件、付録Bは68件、unsure 0。

| 範囲 | own | mathlib | partial | none | unsure | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| A.1 | 0 | 0 | 1 | 16 | 0 | 17 |
| A.2 | 0 | 0 | 1 | 9 | 0 | 10 |
| A.3 | 0 | 0 | 2 | 8 | 0 | 10 |
| A.4 | 0 | 0 | 1 | 18 | 0 | 19 |
| A.5 | 0 | 2 | 1 | 16 | 0 | 19 |
| A.6 | 0 | 0 | 1 | 10 | 0 | 11 |
| A.7 | 0 | 0 | 2 | 9 | 0 | 11 |
| A.8 | 0 | 0 | 0 | 20 | 0 | 20 |
| A.9 | 0 | 0 | 1 | 17 | 0 | 18 |

| 範囲 | own | mathlib | partial | none | unsure | 合計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| B.0 | 0 | 0 | 0 | 10 | 0 | 10 |
| B.1 | 0 | 0 | 1 | 13 | 0 | 14 |
| B.2 | 0 | 0 | 1 | 10 | 0 | 11 |
| B.3 | 0 | 0 | 4 | 17 | 0 | 21 |
| B.4 | 1 | 0 | 1 | 10 | 0 | 12 |

A：mathlib 2・partial 10・none 123。B：own 1・partial 7・none 60。全partial 17件を四分類で見直した。none 183件は行ごとに原典・両ソース・引用と隣節を比較し、§4の3′は使っていない。

- **Aの直接対応**：upper-set位相、逆の厳密順序のwell-founded性による昇鎖条件と無限上昇列の非存在は原典の定義・同値に一致する。抽象単体複体は非空有限faceの下方閉族の部分に対応する。
- **通常の層の限界**：定数層をconstantSheafの本質像で定義し、追加のfully faithful仮定の下でcounitによる定数性を判定できる。集合値層のstalk同型判定もある。空間値層のshape、hypercompletion、foliation、constructible sheafの全理論への比較はない。
- **細分とexit paths**：sdとexの随伴はあるが、拡大posetによるmapping cylinderの実現の同相とsmall singular simplexの弱同値比較はない。底上のrelativeFunctorSpaceとleft fibrationの場合のKan性はA.4.17・A.7.3–4・A.9.2の値の式に対応する。SingA(X)自体、conical仮定からのinner fibration、exit-path van Kampen、constructible sheafとの全圏同値は未対応。
- **recollement**：nativeな安定lax pullback、DG gluingのstable構造、完全包含・二随伴・kernelを持つ半直交分解は実在する。HAの任意recollementをその模型へ表示する圏同値と全五条件の比較がなく、A.8の一般理論をこれらの類似だけでpartialとはしない。
- **Bの直接対応**：B.4.4は任意の単体集合の射の引き戻し関手に右随伴が存在する宣言とその随伴のHom全単射から、依存積π∗Xの普遍性を得る（own）。coCartesian fibrationのinner hornと全inner-anodyne逆像の前合成同値はB.3.4・11・14の適用範囲に部分対応する。
- **Bの不足**：marked simplicial set上の一般categorical pattern、P-anodyne、P-fiberedの全六条件、対応するleft proper combinatorial simplicial model構造と全Quillen functorialityはない。flatnessはcoCartesianの場合の逆像同値を確認したが、任意inner fibrationのfactorization圏によるiffは未対応。定数束のfiberwiseHomのCartesian性を一般flat π・任意φの右Quillen性と同一視しない。

全対応宣言の型・公理とソースハッシュを検証し、追加公理はない。
