module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentInjectiveNaturality
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ThinNerveEvaluation

/-!
# 順序写像による Path の旗の像

概要：Path の旗の一座標の像が既知の点なら、その前後の頂点は同じである。
方針：各頂点を端点と既に加わった内部座標の像で表す。
規約：像で両端が一致する場合も許す。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の退化方向の消滅。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening
open scoped _root_.Simplicial
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：有限内部点の旗を Path に入れ、順序写像で送った旗。
方針：native な二つの関手を合成する。
規約：番号付けの全ての順序を許す。
使われ方：Kerodon 2.5.9（Tag 00SC） の各置換に対応する旗の退化判定。 -/
def pathImageFlag (f : J →o K) (hab : a < b) (S : Finset (Set.Ioo a b))
    {m : ℕ} (e : Fin m ≃ S) : (nerve (Path (f a) (f b))) _⦋m⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlag e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeFunctor hab S ⋙ SimplicialThickening.functorMap f (.mk a) (.mk b)

/-- 概要：像の旗の各頂点は端点の像と既に加わった内部座標の像からなる。
方針：Path への包含と順序写像の像の所属を展開する。
規約：部分型の所属証明は値を変えない。
使われ方：HA 1.3.1.16 の退化する旗の隣接頂点の計算。 -/
lemma mem_pathImageFlag_obj (f : J →o K) (hab : a < b) (S : Finset (Set.Ioo a b))
    {m : ℕ} (e : Fin m ≃ S) (t : Fin (m + 1)) (z : K) :
    z ∈ ((pathImageFlag f hab S e).obj t).I ↔
      z = f a ∨ z = f b ∨ ∃ v : S, (e.symm v).val < t.val ∧ f v.val.val = z := by
  change (z ∈ f '' {x | x = a ∨ x = b ∨ ∃ h : x ∈ Set.Ioo a b,
    (⟨x, h⟩ : Set.Ioo a b) ∈ (Subtype.val : S → Set.Ioo a b) ''
      {v | (e.symm v).val < t.val}}) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | ⟨hx, v, hv, he⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨v, hv, congrArg f (congrArg Subtype.val he)⟩)
  · rintro (rfl | rfl | ⟨v, hv, rfl⟩)
    · exact ⟨a, Or.inl rfl, rfl⟩
    · exact ⟨b, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨v.val.val, Or.inr (Or.inr ⟨v.val.property, v, hv, rfl⟩), rfl⟩

/-- 概要：加える座標の像が端点か先行する座標の像なら、像の旗の隣接頂点は等しい。
方針：新しい座標だけを分離し、その像を既知の点で置き換える。
規約：先行性は元の線形順序でなく旗の番号付けに関する。
使われ方：Kerodon 2.5.9（Tag 00SC） の全ての置換の旗の退化を検出する。 -/
lemma pathImageFlag_repeat (f : J →o K) (hab : a < b) (S : Finset (Set.Ioo a b))
    {n : ℕ} (e : Fin n ≃ S) (i : Fin n)
    (hi : f (e i).val.val = f a ∨ f (e i).val.val = f b ∨
      ∃ j : Fin n, j.val < i.val ∧ f (e j).val.val = f (e i).val.val) :
    (pathImageFlag f hab S e).obj i.castSucc =
      (pathImageFlag f hab S e).obj i.succ := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  apply Set.ext
  intro z
  rw [mem_pathImageFlag_obj, mem_pathImageFlag_obj]
  constructor
  · rintro (h | h | ⟨v, hv, he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · change (e.symm v).val < i.val at hv
      exact Or.inr (Or.inr ⟨v, by change (e.symm v).val < i.val + 1; omega, he⟩)
  · rintro (h | h | ⟨v, hv, he⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases hvi : (e.symm v).val < i.val
      · exact Or.inr (Or.inr ⟨v, hvi, he⟩)
      · have hidx : e.symm v = i := Fin.ext (by
          change (e.symm v).val < i.val + 1 at hv
          omega)
        have hv' : v = e i := by simpa using congrArg e hidx
        subst v
        rcases hi with ha | hb | ⟨j, hj, hji⟩
        · exact Or.inl (he.symm.trans ha)
        · exact Or.inr (Or.inl (he.symm.trans hb))
        · exact Or.inr (Or.inr ⟨e j, by simpa using hj, hji.trans he⟩)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
