module

public import SerrePositivity.CategoryTheory.Simplex.PresentationDegeneracies

/-!
# 表示された単体圏から通常の単体圏への写像は面の標準形を区別する

## 概要
表示された単体圏から通常の単体圏への写像は面の標準形を区別する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0044][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0044
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Face normal forms in the presented simplex category
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory SimplexCategoryGenRel

namespace SerrePositivity.SimplexPresentation

def standardδ (L : List ℕ) {m n : ℕ} (h : m + L.length = n) : mk m ⟶ mk n :=
  match L with
  | [] => eqToHom (by simp only [List.length_nil, Nat.add_zero] at h; exact congrArg mk h)
  | a :: L => δ (Fin.ofNat (m + 2) a) ≫ standardδ L (by simp_all; omega)

@[simp] lemma standardδ_nil (m : ℕ) : standardδ [] (m := m) rfl = 𝟙 _ := rfl

@[simp, reassoc] lemma standardδ_cons (a : ℕ) (L : List ℕ) {m n : ℕ}
    (h : m + (a :: L).length = n) :
    standardδ (a :: L) h = δ (Fin.ofNat (m + 2) a) ≫ standardδ L (by simp_all; omega) := rfl

lemma standardδ_comp (L K : List ℕ) {m n p : ℕ}
    (h : m + L.length = n) (h' : n + K.length = p) :
    standardδ L h ≫ standardδ K h' = standardδ (L ++ K) (by simp_all; omega) := by
  induction L generalizing m n p with
  | nil => subst n; simp
  | cons a L ih => simp only [standardδ_cons, Category.assoc, ih, List.cons_append]

lemma standardδ_simplicialInsert {m : ℕ} (L : List ℕ) (hL : IsAdmissible (m + 2) L)
    (j : ℕ) (hj : j < m + 2) (n : ℕ) (hn : m + L.length + 1 = n) :
    standardδ (simplicialInsert j L) (m := m) (n := n)
        (by rw [simplicialInsert_length]; omega) =
      δ (Fin.ofNat (m + 2) j) ≫ standardδ L (by omega) := by
  induction L generalizing m j with
  | nil => simp [standardδ, simplicialInsert]
  | cons a L ih =>
    simp only [List.length_cons] at hn
    simp only [simplicialInsert]
    split_ifs with hja
    · simp
    · have ha : a < m + 2 := by omega
      have hex : δ (Fin.ofNat (m + 2) j) ≫ δ (Fin.ofNat (m + 3) a) =
          δ (Fin.ofNat (m + 2) a) ≫ δ (Fin.ofNat (m + 3) (j + 1)) := by
        have ofNat_eq (k t : ℕ) (ht : t < k + 1) : Fin.ofNat (k + 1) t = ⟨t, ht⟩ := by
          ext; simp [Nat.mod_eq_of_lt ht]
        simpa only [ofNat_eq (m + 1) a ha, ofNat_eq (m + 1) j hj,
          ofNat_eq (m + 2) a (by omega), ofNat_eq (m + 2) (j + 1) (by omega)] using
          (δ_comp_δ_nat (n := m) a j ha hj (by omega)).symm
      rw [standardδ_cons, ih (m := m + 1) hL.of_cons (j + 1) (by omega) (by omega),
        ← Category.assoc, ← hex, Category.assoc]
      rfl

lemma exists_normal_form_faces {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_δ f) :
    ∃ (L : List ℕ) (m n : ℕ) (hx : x = mk m) (hy : y = mk n)
      (hlen : m + L.length = n), IsAdmissible (m + 1) L ∧
      f = eqToHom hx ≫ standardδ L hlen ≫ eqToHom hy.symm := by
  change faces.multiplicativeClosure f at hf
  rw [MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure'] at hf
  induction hf with
  | id x =>
    exact ⟨[], x.len, x.len, rfl, rfl, by simp, .nil _, by simp⟩
  | of f hf =>
    cases hf with | @δ m i =>
    exact ⟨[i.val], m, m + 1, rfl, rfl, rfl, .singleton i.is_le, by simp⟩
  | @of_comp x y z f g hf hg ih =>
    cases hf with | @δ m i =>
    obtain ⟨L, m', n, hx, hy, hlen, hL, hform⟩ := ih
    have hm : m' = m + 1 := (congrArg SimplexCategoryGenRel.len hx).symm
    subst m'
    obtain rfl : z = mk n := hy
    refine ⟨simplicialInsert i.val L, m, n, rfl, rfl, ?_,
      simplicialInsert_isAdmissible (m + 1) L hL i.val i.is_le, ?_⟩
    · rw [simplicialInsert_length]; omega
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hform ⊢
      rw [hform, standardδ_simplicialInsert L hL i.val i.is_lt n (by omega)]
      simp

lemma standardδ_faces (L : List ℕ) {m n : ℕ} (h : m + L.length = n) :
    P_δ (standardδ L h) := by
  induction L generalizing m with
  | nil => simp only [List.length_nil, Nat.add_zero] at h; subst n; exact P_δ.id_mem _
  | cons a L ih => exact P_δ.comp_mem _ _ (P_δ.δ _) (ih _)

lemma standardδ_fixed (L : List ℕ) {m n : ℕ} (h : m + L.length = n)
    (hL : IsAdmissible (m + 1) L) (j : ℕ) (hj : j < m + 1)
    (hbelow : ∀ a ∈ L, j < a) :
    ((toSimplexCategory.map (standardδ L h)).toOrderHom ⟨j, hj⟩ : ℕ) = j := by
  induction L generalizing m with
  | nil => simp only [List.length_nil, Nat.add_zero] at h; subst n; rfl
  | cons a L ih =>
    have ha : a < m + 2 := by have := (isAdmissible_cons_iff.mp hL).1; omega
    have hja : j < a := hbelow a (by simp)
    have he : (Fin.ofNat (m + 2) a).succAbove ⟨j, hj⟩ = ⟨j, by omega⟩ := by
      rw [Fin.succAbove_of_castSucc_lt]
      · rfl
      · change j < a % (m + 2)
        rwa [Nat.mod_eq_of_lt ha]
    rw [standardδ_cons, CategoryTheory.Functor.map_comp, toSimplexCategory_map_δ]
    change (((toSimplexCategory.map (standardδ L _)).toOrderHom)
      ((Fin.ofNat (m + 2) a).succAbove ⟨j, hj⟩) : ℕ) = j
    rw [he]
    exact ih _ hL.of_cons (by omega) (fun b hb => hbelow b (by simp [hb]))

lemma standardδ_range (L : List ℕ) {m n : ℕ} (h : m + L.length = n)
    (hL : IsAdmissible (m + 1) L) (k : Fin (n + 1)) :
    (∃ j, (toSimplexCategory.map (standardδ L h)).toOrderHom j = k) ↔ k.val ∉ L := by
  induction L generalizing m with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at h
    subst n
    exact ⟨fun _ => by simp, fun _ => ⟨k, rfl⟩⟩
  | cons a L ih =>
    have ha : a < m + 2 := by have := (isAdmissible_cons_iff.mp hL).1; omega
    have htail : m + 1 + L.length = n := by simp only [List.length_cons] at h; omega
    let a₀ : Fin (m + 2) := ⟨a, ha⟩
    let t := (toSimplexCategory.map (standardδ L (m := m + 1) (n := n) htail)).toOrderHom
    have ht : (t a₀ : ℕ) = a :=
      standardδ_fixed L htail hL.of_cons a ha (fun b hb => hL.head_lt b hb)
    have : IsSplitMono (toSimplexCategory.map (standardδ L (m := m + 1) (n := n) htail)) :=
      isSplitMono_toSimplexCategory_map_of_P_δ (standardδ_faces L htail)
    have hinj : Function.Injective t := SimplexCategory.mono_iff_injective.mp inferInstance
    have hof : Fin.ofNat (m + 2) a = a₀ := by ext; exact Nat.mod_eq_of_lt ha
    rw [standardδ_cons, CategoryTheory.Functor.map_comp, toSimplexCategory_map_δ]
    change (∃ j : Fin (m + 1), t ((Fin.ofNat (m + 2) a).succAbove j) = k) ↔ _
    rw [hof]
    constructor
    · rintro ⟨j, hj⟩
      have hka : k.val ≠ a := by
        intro hka
        have he : t (a₀.succAbove j) = t a₀ := by apply Fin.ext; omega
        exact Fin.succAbove_ne a₀ j (hinj he)
      have hkL : k.val ∉ L := (ih _ hL.of_cons).mp ⟨_, hj⟩
      simpa only [List.mem_cons, not_or] using And.intro hka hkL
    · intro hk
      have hk' : k.val ≠ a ∧ k.val ∉ L := by simpa only [List.mem_cons, not_or] using hk
      obtain ⟨j, hj⟩ := (ih _ hL.of_cons).mpr hk'.2
      have hja : j ≠ a₀ := by intro he; subst j; exact hk'.1 (hj ▸ ht)
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hja
      exact ⟨i, hi ▸ hj⟩

lemma standardδ_injective {m n : ℕ} {L K : List ℕ}
    (hL : IsAdmissible (m + 1) L) (hK : IsAdmissible (m + 1) K)
    (hLn : m + L.length = n) (hKn : m + K.length = n)
    (h : toSimplexCategory.map (standardδ L hLn) =
      toSimplexCategory.map (standardδ K hKn)) : L = K := by
  apply hL.sortedLT.eq_of_mem_iff hK.sortedLT
  intro j
  by_cases hj : j < n + 1
  · have hr := congrArg (fun f : SimplexCategory.mk m ⟶ SimplexCategory.mk n =>
        ∃ i, f.toOrderHom i = ⟨j, hj⟩) h
    exact not_iff_not.mp ((standardδ_range L hLn hL ⟨j, hj⟩).symm.trans
      ((iff_of_eq hr).trans (standardδ_range K hKn hK ⟨j, hj⟩)))
  · have hnL : j ∉ L := by
      intro hm
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
      have := hL.getElem_lt (hk := hi)
      omega
    have hnK : j ∉ K := by
      intro hm
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
      have := hK.getElem_lt (hk := hi)
      omega
    simp only [hnL, hnK]

/-- 表示された単体圏から通常の単体圏への写像は面の標準形を区別する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。
-/
lemma map_injective_on_faces {x y : SimplexCategoryGenRel} {f g : x ⟶ y}
    (hf : P_δ f) (hg : P_δ g) (h : toSimplexCategory.map f = toSimplexCategory.map g) :
    f = g := by
  obtain ⟨L, m, n, rfl, rfl, hLn, hL, hf'⟩ := exists_normal_form_faces f hf
  obtain ⟨K, m', n', hx, hy, hKn, hK, hg'⟩ := exists_normal_form_faces g hg
  have hm : m' = m := (congrArg SimplexCategoryGenRel.len hx).symm
  have hn : n' = n := (congrArg SimplexCategoryGenRel.len hy).symm
  subst m'; subst n'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf' hg'
  have heq : L = K := standardδ_injective hL hK hLn hKn (by simpa only [hf', hg'] using h)
  subst K
  exact hf'.trans hg'.symm

end SerrePositivity.SimplexPresentation
