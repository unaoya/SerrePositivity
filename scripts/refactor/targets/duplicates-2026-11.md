# EInfinity の同名宣言（2026-11、段 G の候補）

`SerrePositivity.EInfinity.Hammock.Word.eq_empty_of_length_zero` は、長さ零の語が空語に等しいという補題で、二つのソースがそれぞれ定義している。§10.21 に従い、保存検査では定義元モジュールごとに2行を保持する。

| 定義元（`SerrePositivity.EInfinity.Hammock` 以下） | 箇所 | 証明 |
|---|---|---|
| `LengthZero` | [LengthZero.lean:23](../../../SerrePositivity/EInfinity/Hammock/LengthZero.lean#L23) | `Word.object_ext` と空の添字型の消去を使う |
| `WordCons` | [WordCons.lean:27](../../../SerrePositivity/EInfinity/Hammock/WordCons.lean#L27) | 語を分解し、長さを代入して向きの関数の等式を示す |

型・公理・属性・種類は一致し、証明が使う定数と定義位置は異なる。整理は証明を変更する段 G で R80 とともに検討する。
