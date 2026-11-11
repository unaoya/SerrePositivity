module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# 同じ射の有限個の押し出し

## 概要
一つの射に沿う二項押し出しから、その射を有限個並べた広い押し出しを作る。

## 方針
有限集合の最初の脚を二項押し出しの左脚とし、残りを帰納法でまとめる。

## 規約
環構造に依らない余極限。空添字の場合も基底を残す。

## 使われ方
BS 著者版 Corollary 3.12 の完備 Čech 余脈体。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X Y : C}

/-- 同じ射を指定個数だけ並べた広い span。 -/
abbrev repeatedWideSpan (f : X ⟶ Y) (n : ℕ) :=
  WidePushoutShape.wideSpan X (fun _ : Fin n ↦ Y) (fun _ ↦ f)

private theorem repeated_condition {f : X ⟶ Y} {n : ℕ}
    (s : Cocone (repeatedWideSpan f n)) (i : Fin n) :
    f ≫ s.ι.app (some i) = s.ι.app none := by
  simpa using s.w (WidePushoutShape.Hom.init i)

/-- 概要：広い押し出しの cocone に同じ射を一つ加えるには二項押し出しで十分。
方針：最初の脚と残りの脚を分離して、双方の普遍性を用いる。
規約：添字は `Fin (n+1)`。
使われ方：完備押し出しと有限剰余の押し出しの両方に適用する。 -/
def repeatedWideSpanSuccIsColimit {f : X ⟶ Y} {n : ℕ}
    {s : Cocone (repeatedWideSpan f n)} (hs : IsColimit s)
    {W : C} {i : Y ⟶ W} {j : s.pt ⟶ W} (h : IsPushout f (s.ι.app none) i j) :
    IsColimit (WidePushoutShape.mkCocone (F := repeatedWideSpan f (n + 1))
      (f ≫ i) (Fin.cases i (fun k ↦ s.ι.app (some k) ≫ j))
      (fun k ↦ Fin.cases rfl
        (fun k ↦ by
          change f ≫ (s.ι.app (some k) ≫ j) = f ≫ i
          rw [← Category.assoc, repeated_condition, h.w]) k)) := by
  let tail (t : Cocone (repeatedWideSpan f (n + 1))) : Cocone (repeatedWideSpan f n) :=
    WidePushoutShape.mkCocone (t.ι.app none) (fun k ↦ t.ι.app (some k.succ))
      (fun k ↦ repeated_condition t k.succ)
  have hw (t : Cocone (repeatedWideSpan f (n + 1))) :
      f ≫ t.ι.app (some 0) = s.ι.app none ≫ hs.desc (tail t) := by
    rw [hs.fac]
    exact repeated_condition t 0
  let d (t : Cocone (repeatedWideSpan f (n + 1))) := h.desc _ _ (hw t)
  have hzero (t : Cocone (repeatedWideSpan f (n + 1))) :
      i ≫ d t = t.ι.app (some 0) := h.inl_desc _ _ _
  have hsucc (t : Cocone (repeatedWideSpan f (n + 1))) (k : Fin n) :
      (s.ι.app (some k) ≫ j) ≫ d t = t.ι.app (some k.succ) := by
    rw [Category.assoc, show j ≫ d t = hs.desc (tail t) from h.inr_desc _ _ _]
    exact hs.fac (tail t) (some k)
  have hbase (t : Cocone (repeatedWideSpan f (n + 1))) :
      (f ≫ i) ≫ d t = t.ι.app none := by
    rw [Category.assoc, hzero, repeated_condition]
  refine ⟨d, ?_, ?_⟩
  · intro t k
    rcases k with _ | k
    · exact hbase t
    · exact Fin.cases (hzero t) (hsucc t) k
  · intro t m hm
    apply h.hom_ext
    · exact (hm (some 0)).trans (hzero t).symm
    · rw [show j ≫ d t = hs.desc (tail t) from h.inr_desc _ _ _]
      apply hs.hom_ext
      rintro (_ | k)
      · rw [hs.fac, ← Category.assoc, ← h.w]
        exact hm none
      · rw [hs.fac, ← Category.assoc]
        exact hm (some k.succ)

/-- 概要：任意の脚に沿う押し出しがあれば、指定した射の有限広押し出しが存在する。
方針：空の場合は基底の恒等射、後続の場合は一脚を追加する。
規約：対象を取り替える被覆の底変換を許す。
使われ方：大域的な余極限の仮定なしで `Arrow.augmentedCechConerve` を作る。 -/
theorem hasWidePushout_repeated (f : X ⟶ Y)
    (h : ∀ ⦃Z : C⦄ (g : X ⟶ Z), HasPushout f g) (n : ℕ) :
    HasWidePushout X (fun _ : Fin n ↦ Y) (fun _ ↦ f) := by
  induction n with
  | zero =>
      let s : Cocone (repeatedWideSpan f 0) :=
        WidePushoutShape.mkCocone (𝟙 X) (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)
      refine ⟨⟨s, ⟨fun t ↦ t.ι.app none, ?_, ?_⟩⟩⟩
      · intro t j
        rcases j with _ | j
        · exact Category.id_comp _
        · exact Fin.elim0 j
      · intro t m hm
        simpa [s] using hm none
  | succ n ih =>
      letI : HasColimit (repeatedWideSpan f n) := ih
      let s := colimit.cocone (repeatedWideSpan f n)
      letI := h (s.ι.app none)
      let hs := repeatedWideSpanSuccIsColimit (colimit.isColimit (repeatedWideSpan f n))
        (IsPushout.of_hasPushout f (s.ι.app none))
      exact ⟨⟨_, hs⟩⟩

end CategoryTheory.Limits
