# drafts：BS の設計段階の Lean の骨組み（ビルドしない）

概要：E3 を消す道筋（stage2 の A 案）の設計段階で書く Lean の骨組み。主張の型と `sorry` の証明だけで、**ビルド・`lake env lean`・監査を
一切行わない**（coordination.md §1 の BS の行、2026-11-02）。`SerrePositivity/` の外にあるので root からも監査からも届かない。
方針：各ファイルは、将来置かれる場所のモジュール名を先頭のコメントに書く（例：`SerrePositivity.InfinityCategories.Sheaves.SheafCondition`）。
import 行は現時点の main の名前で書く（基準コミットは下の表）。論文の層の整理（2a・2b）や ∞ の束で名前が変わったら、調整役から回る
旧→新の対応表で直す（`scripts/move_module.py` が自動で直すこともある）。
規約：docstring は README の Conventions（概要／方針／規約／使われ方）。宣言名は内容の名前（原典の番号は docstring に）。
`sorry` には理由を一行添える（「S3 の補題を待つ」「2b の後に HA を読んでから」など）。新しい `axiom` は置かない。
使われ方：中身を書く段階（暦に載せてから）で、該当するファイルを `SerrePositivity/` の下の決まった場所へ移し、単体の `lake build` で確かめる。
設計書は [infinity-sheaves-design.md](../infinity-sheaves-design.md)・[a0-design.md](../a0-design.md)。

| ディレクトリ | 将来の置き場所（調整役の決定、main d9254e8b0） | 設計書の単位 |
| --- | --- | --- |
| `Sheaves/` | `SerrePositivity/InfinityCategories/Sheaves/`（層の順序 StablePresentable < Sheaves < ModelBridge。最初のファイルで `scripts/refactor/layers.json` に登録） | S1〜S6 |
| `DerivedSheaves/` | `SerrePositivity/InfinityCategories/Derived/Sheaves/` | S7（D(A) への適用） |
| `A0/` | `SerrePositivity/BhattScholze/Prismatic/`（仮） | A0-1〜A0-4 |
| `A1/` | `SerrePositivity/BhattScholze/Prismatic/`（仮） | A1-1〜A1-4 |
| `A2/` | `SerrePositivity/BhattScholze/Prismatic/Derived/`（仮） | A2-1〜A2-4 |
| `A3/` | `SerrePositivity/BhattScholze/Prismatic/Derived/`（仮） | A3-1〜A3-4 |
| `A4/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（既存の Interface.lean の隣。E3 の欄の構成なので Prismatic/ ではなく Perfectoidization/。調整役了承、main 431c40741） | A4-1〜A4-4 |
| `A5/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き） | A5-1〜A5-4 |
| `A6/` | `SerrePositivity/BhattScholze/Perfectoidization/Derived/`（A4 と同じ仮置き。arc site は BS 固有の扱い） | A6-1〜A6-4 |
| `Sheaves/SpaceValued` | S8（空間値の層、0 切り捨て、E 値の層の局所性）。`InfinityCategories/Sheaves/` の続きか別層か、置き場所と担当は調整役（未回答） | S8 |
| `Shared/Descendable` | `SerrePositivity/EInfinity/Descendable/`（新設。CAlg と D(A) の両方を使う。調整役の決定、main 86acd98db、infinity-foundation-plan.md の M15）。E∞ を使わない thick ⊗-ideal・index・安定性の部分は Derived/ へ下ろしてよい。時期・担当は M14 と同じ（段 G、A5 の中身を書く段階）。それまで drafts/Shared/ のまま | G-A5-1 |
| `DerivedGeneral/` | `SerrePositivity/InfinityCategories/Derived/`（調整役の決定、main 600e578d7、infinity-foundation-plan.md の M13。Derived は HA を import 済みなので PDCompletion への依存は可。一般の t 構造の定義を切り出すなら Stable/）。時期は段 G、W2b の後。CompletionFunctor は 2b の改名表を受けてから。それまで drafts/DerivedGeneral/ のまま | G-A2-2・G-A2-3 |
| `Shared/` | 共有層（調整役の決定、main 26f1f4d94）：cup 積・Bockstein は `HomologicalAlgebra/Cosimplicial/`、de Rham は `CommutativeAlgebra/DeRham/`（いずれも新設、HA の第一層＝一般論の扱い）。移すのは 2b の後。名前は論文の層に予約してもらう。それまで drafts/Shared/ のまま | G-A1-1・2・9 ほか |
| `Shared/EInfinityPowerOperation` | `SerrePositivity/EInfinity/PowerOperation/`（新設、BarrattEccles・Operad の隣。調整役の決定、main 431c40741、infinity-foundation-plan.md の M14）。Barratt–Eccles の作用の型はそこで確認。時期は A4 の中身を書く段階、担当（E2 レーンか BS か）はそのとき決める。それまで drafts/Shared/ のまま | G-A4-1 |

| 基準コミット | 日付 | 内容 |
| --- | --- | --- |
| 972bb7f53 | 2026-11-02 | 最初の骨組み（S1・S2）。InfinityCategories の名前はこの時点の main |
