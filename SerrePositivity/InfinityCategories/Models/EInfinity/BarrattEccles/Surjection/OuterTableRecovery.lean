module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterSelection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 合成表全体から外側表の抽出成功を復元

概要：Berger–Fresse §1.5.8 の合成置換行列の外側射影を実際の抽出へ移す。
方針：各行の縮約した選択語を行長にし、復元状態での一行の転送を反復する。
規約：垂直移動による外側置換の繰り返しはこの段階では保持する。
使われ方：重複外側行を融合し、元の外側成功表を得る逆構成。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内外の置換と行長の列が定める実際の合成表（BF §1.5.8）。
方針：各組の置換を部分合成し、逆置換行と元の行長を保持する。
規約：成分は外側置換・内側置換・正値性をまだ課さない自然数行長。
使われ方：任意の成功経路表を外側復元へ渡す。 -/
def mixedTable {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ)) :
    List (List (Fin (m + n)) × ℕ) :=
  entries.map (fun p => (List.ofFn (permutationComposition m n k p.1 p.2.1).symm, p.2.2))

/-- 概要：合成選択語から各外側選択長を復元した表（BF §1.5.8）。
方針：元の外側逆置換行に対応する選択語の外側縮約長を付ける。
規約：元の外側置換の繰り返しは除去しない。
使われ方：合成の抽出成功から実際の外側抽出成功を構成する。 -/
def recoveredOuterTable {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (picked : List (List (Fin (m + n)))) : List (List (Fin (m + 1)) × ℕ) :=
  List.zipWith (fun p word => (List.ofFn p.1.symm, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k word).length)) entries picked

/-- 概要：合成表の有限先行部分は復元外側表と任意の後続へ転送できる（BF §1.5.8）。
方針：実際の先行抽出で帰納し、各行の除外集合の復元一致を後続へ渡す。
規約：選択語の外側縮約を各行ごとに連結し、重複する外側行は保持する。
使われ方：全合成表から外側表の成功を構成し、その後の共有行融合へつなぐ。 -/
lemma outer_prefix_success {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked finish)
    (rest : List (List (Fin (m + 1)) × ℕ)) (tail : List (Fin (m + 1)))
    (hrest : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k finish) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked ++ rest) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) =
      some ((picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten ++ tail) := by
  induction entries generalizing removed picked with
  | nil => cases hpre; simpa [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable] using hrest
  | cons entry entries ih =>
    obtain ⟨σ, τ, r⟩ := entry
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries)
      removed picked finish at hpre
    cases hpre with
    | @cons _ _ _ _ picked _ hr hb ht =>
      have htail := ih _ _ ht
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerSelection_step k σ τ removed r hr hb
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked ++ rest)
        ((picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten ++ tail) htail
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable, List.zipWith_cons_cons, List.cons_append,
        List.map_cons, List.flatten_cons, List.append_assoc] using hs

/-- 概要：任意の合成表の成功から外側表の成功を復元できる（BF §1.5.8）。
方針：合成成功を全行の先行抽出に分解し、空の後続で外側転送を閉じる。
規約：元の選択語と終状態も証跡として返し、外側置換の重複は保持する。
使われ方：shuffle 経路表から元の外側表へ戻す全体の第一段。 -/
lemma outer_table_success {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed = some out) :
    ∃ picked finish, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) removed picked finish ∧
      out = picked.flatten ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerRemoved k removed) =
        some (picked.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerWord k)).flatten := by
  obtain ⟨picked, finish, tail, hp, ht, ho⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.extractionPrefix_of_reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k entries) [] removed out (by simpa using h)
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_nil, Option.some.injEq] at ht
  subst tail
  refine ⟨picked, finish, hp, ?_, ?_⟩
  · simpa only [List.append_nil] using ho
  · simpa only [List.append_nil] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outer_prefix_success k entries removed finish picked hp
      [] [] rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
