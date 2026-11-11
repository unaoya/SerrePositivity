module
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Option.Basic


/-!
概要：smash の単体を非基点の組または基点として表示するための集合の計算。
方針：基点を含む組を none へ潰し、それ以外を some へ送る。
規約：純粋な集合の補題であり、単体作用と既存の smash との同型は別途与える。
使われ方：BF 1978 §2、HTT 4.2.4.1 の Sp の積の懸垂構造射の単射性。
-/

@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

noncomputable section

/-- 概要：二つの基点付き集合の非基点の組と一つの基点。
方針：両成分が非基点の部分型へ Option を付ける。
規約：none が基点。
使われ方：smash の各単体次数での具体的な表示。 -/
abbrev SmashSimplex {A B : Type u} (a₀ : A) (b₀ : B) :=
  Option {p : A × B // p.1 ≠ a₀ ∧ p.2 ≠ b₀}

/-- 概要：組のどちらかが基点なら基点へ潰す標準写像。
方針：二成分の基点との等号で場合分けする。
規約：古典的な等号の判定を使い、非基点の組はそのまま保持する。
使われ方：smash の商の各次数の標準射の表示。 -/
def smashSimplexPack {A B : Type u} (a₀ : A) (b₀ : B) (a : A) (b : B) :
    SmashSimplex a₀ b₀ := by
  classical
  exact if ha : a = a₀ then none else if hb : b = b₀ then none else some ⟨(a, b), ha, hb⟩

/-- 概要：標準写像が基点へ送る組はどちらかの成分が基点の組。
方針：二つの等号の判定を計算する。
規約：全ての基点付き集合で成立する。
使われ方：smash の商の核の識別。 -/
lemma smashSimplexPack_eq_none {A B : Type u} (a₀ : A) (b₀ : B) (a : A) (b : B) :
    smashSimplexPack a₀ b₀ a b = none ↔ a = a₀ ∨ b = b₀ := by
  classical
  by_cases ha : a = a₀ <;> by_cases hb : b = b₀ <;> simp [smashSimplexPack, ha, hb]

/-- 概要：smash の表示の各元は組の標準写像で表せる。
方針：基点は基点の組、それ以外は記録された非基点の組で表す。
規約：空である可能性のある非基点部分にも適用する。
使われ方：単体作用の法則と射の等式を代表の組で検査する。 -/
lemma smashSimplexPack_surjective {A B : Type u} (a₀ : A) (b₀ : B) :
    ∀ s : SmashSimplex a₀ b₀, ∃ a b, smashSimplexPack a₀ b₀ a b = s := by
  classical
  rintro (_ | ⟨⟨a, b⟩, ha, hb⟩)
  · exact ⟨a₀, b₀, by simp [smashSimplexPack]⟩
  · exact ⟨a, b, by simp [smashSimplexPack, ha, hb]⟩

/-- 概要：二つの組の標準写像の像が等しいのは、同じ組か両方が基点へ潰れる場合。
方針：各成分の基点との等号で場合分けし、非基点の部分型の値を比較する。
規約：非基点を保持することを全ての集合について明示する。
使われ方：smash と積の比較の単射性の核の計算。 -/
lemma smashSimplexPack_eq_iff {A B : Type u} (a₀ : A) (b₀ : B)
    (a a' : A) (b b' : B) :
    smashSimplexPack a₀ b₀ a b = smashSimplexPack a₀ b₀ a' b' ↔
      (a = a' ∧ b = b') ∨ ((a = a₀ ∨ b = b₀) ∧ (a' = a₀ ∨ b' = b₀)) := by
  classical
  by_cases ha : a = a₀ <;> by_cases ha' : a' = a₀ <;>
    by_cases hb : b = b₀ <;> by_cases hb' : b' = b₀ <;>
    simp_all [smashSimplexPack] <;> aesop

/-- 概要：基点を保つ二つの写像を smash の表示へ写す。
方針：基点は保持し、非基点の組の像を再び標準写像でまとめる。
規約：像が基点へ潰れる場合も許す。
使われ方：面・退化写像と smash の射の各次数の構成。 -/
def smashSimplexMap {A B C D : Type u} {a₀ : A} {b₀ : B} (c₀ : C) (d₀ : D)
    (f : A → C) (g : B → D) : SmashSimplex a₀ b₀ → SmashSimplex c₀ d₀
  | none => none
  | some p => smashSimplexPack c₀ d₀ (f p.val.1) (g p.val.2)

/-- 概要：基点を保つ写像による作用は標準写像と可換。
方針：元の組が基点を含むかどうかで場合分けする。
規約：二つの写像の基点保存を明示する。
使われ方：smash の単体作用と関手性の検証。 -/
lemma smashSimplexMap_pack {A B C D : Type u} {a₀ : A} {b₀ : B} {c₀ : C} {d₀ : D}
    (f : A → C) (g : B → D) (hf : f a₀ = c₀) (hg : g b₀ = d₀) (a : A) (b : B) :
    smashSimplexMap c₀ d₀ f g (smashSimplexPack a₀ b₀ a b) =
      smashSimplexPack c₀ d₀ (f a) (g b) := by
  classical
  by_cases ha : a = a₀ <;> by_cases hb : b = b₀ <;>
    simp_all [smashSimplexPack, smashSimplexMap]

/-- 概要：積を右因子に持つ smash の表示を二つの射影で比較する写像。
方針：左成分を保ち、右成分の二つの射影を取る。
規約：右因子の基点は基点の組。
使われ方：BF 1978 §2 の二項積の懸垂構造射の単射性。 -/
def smashSimplexProductComparison {A B C : Type u} (a₀ : A) (b₀ : B) (c₀ : C) :
    SmashSimplex a₀ (b₀, c₀) → SmashSimplex a₀ b₀ × SmashSimplex a₀ c₀ :=
  fun s ↦ (smashSimplexMap a₀ b₀ id Prod.fst s, smashSimplexMap a₀ c₀ id Prod.snd s)

/-- 概要：積との比較は組の標準写像を二つの組の標準写像へ送る。
方針：二つの射影に標準写像との可換式を適用する。
規約：全ての組で成立し、基点を含む場合も除外しない。
使われ方：smash と二項積の比較の単射性の計算。 -/
lemma smashSimplexProductComparison_pack {A B C : Type u}
    (a₀ : A) (b₀ : B) (c₀ : C) (a : A) (b : B) (c : C) :
    smashSimplexProductComparison a₀ b₀ c₀ (smashSimplexPack a₀ (b₀, c₀) a (b, c)) =
      (smashSimplexPack a₀ b₀ a b, smashSimplexPack a₀ c₀ a c) := by
  unfold smashSimplexProductComparison
  exact Prod.ext
    (smashSimplexMap_pack (a₀ := a₀) (b₀ := (b₀, c₀)) id Prod.fst rfl rfl a (b, c))
    (smashSimplexMap_pack (a₀ := a₀) (b₀ := (b₀, c₀)) id Prod.snd rfl rfl a (b, c))

/-- 概要：積を右因子に持つ smash の表示は二つの射影の像で識別できる。
方針：組の代表を取り、標準写像の核の等式を二成分で使う。
規約：左成分の基点を共有することを使い、基点の組も扱う。
使われ方：BF 1978 §2、Sp の二項積の懸垂構造射の単射性の集合論的な部分。 -/
lemma smashSimplexProductComparison_injective {A B C : Type u} (a₀ : A) (b₀ : B) (c₀ : C) :
    Function.Injective (smashSimplexProductComparison a₀ b₀ c₀) := by
  intro s t h
  obtain ⟨a, ⟨b, c⟩, rfl⟩ := smashSimplexPack_surjective a₀ (b₀, c₀) s
  obtain ⟨a', ⟨b', c'⟩, rfl⟩ := smashSimplexPack_surjective a₀ (b₀, c₀) t
  rw [smashSimplexProductComparison_pack, smashSimplexProductComparison_pack] at h
  have hb := (smashSimplexPack_eq_iff a₀ b₀ a a' b b').mp (congrArg Prod.fst h)
  have hc := (smashSimplexPack_eq_iff a₀ c₀ a a' c c').mp (congrArg Prod.snd h)
  apply (smashSimplexPack_eq_iff a₀ (b₀, c₀) a a' (b, c) (b', c')).mpr
  simp only [Prod.mk.injEq]
  aesop

end

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
