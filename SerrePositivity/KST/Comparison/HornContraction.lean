module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexContraction
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# horn を保つ標準単体の頂点への収縮

概要：任意の頂点 k に向かう二つのホモトピーを、horn と両立する形で構成する。
方針：min(x,k)≤x と min(x,k)≤k を区間の単調な写像にする。
規約：Segal 1974 Proposition 1.6 の対角模型の補助。原典の fat realization は経由しない。
使われ方：Kan fibration に沿う horn の逆像を比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

/--
概要：頂点の単調な自己写像が標準単体に誘導する写像。
方針：単体の単調写像に後合成する。
規約：Segal 1974 Proposition 1.6 の組合せ的補助。
使われ方：頂点との最小値を取る写像の構成。
-/
def simplexOrderMap {n : ℕ} (f : Fin (n + 1) →o Fin (n + 1)) :
    (Δ[n] : SSet.{u}) ⟶ Δ[n] where
  app _ := TypeCat.ofHom fun s => SSet.stdSimplex.objMk (f.comp (SSet.stdSimplex.asOrderHom s))
  naturality _ _ _ := rfl

/--
概要：点ごとに比較可能な単調写像を区間で結ぶ写像。
方針：区間座標が零なら下の写像、それ以外なら上の写像を使う。
規約：Segal 1974 Proposition 1.6 の頂点への収縮。
使われ方：horn を保つ二つの実ホモトピー。
-/
def simplexOrderHomotopyMap {n : ℕ} (f g : Fin (n + 1) →o Fin (n + 1))
    (hfg : f ≤ g) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n] where
  app _ := TypeCat.ofHom fun p => SSet.stdSimplex.objMk
    { toFun := fun i => if SSet.stdSimplex.asOrderHom p.2 i = 0 then
          f (SSet.stdSimplex.asOrderHom p.1 i) else g (SSet.stdSimplex.asOrderHom p.1 i)
      monotone' := by
        intro i j hij
        by_cases hi : SSet.stdSimplex.asOrderHom p.2 i = 0
        · by_cases hj : SSet.stdSimplex.asOrderHom p.2 j = 0
          · simp only [hi, hj, ↓reduceIte]
            exact f.monotone ((SSet.stdSimplex.asOrderHom p.1).monotone hij)
          · simp only [hi, hj, ↓reduceIte]
            exact (hfg _).trans (g.monotone ((SSet.stdSimplex.asOrderHom p.1).monotone hij))
        · have hj : SSet.stdSimplex.asOrderHom p.2 j ≠ 0 := by
            intro hj
            exact hi (le_antisymm (hj ▸ (SSet.stdSimplex.asOrderHom p.2).monotone hij)
              (Fin.zero_le _))
          simp only [hi, hj, ↓reduceIte]
          exact g.monotone ((SSet.stdSimplex.asOrderHom p.1).monotone hij) }
  naturality _ _ _ := rfl

/--
概要：比較可能な二つの単調写像が誘導する実単体的ホモトピー。
方針：区間の端点を直接評価する。
規約：Segal 1974 Proposition 1.6 の補助。Kan 性は不要。
使われ方：標準単体と horn の同時収縮。
-/
def simplexOrderHomotopy {n : ℕ} (f g : Fin (n + 1) →o Fin (n + 1))
    (hfg : f ≤ g) : SSet.Homotopy (simplexOrderMap f) (simplexOrderMap g) where
  h := simplexOrderHomotopyMap f g hfg
  h₀ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  h₁ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/--
概要：頂点 k との最小値を取る単調写像。
方針：min の単調性を使う。
規約：Segal 1974 Proposition 1.6 の horn の縮約の中間写像。
使われ方：恒等写像と定数写像への二つの比較。
-/
def vertexMeet {n : ℕ} (k : Fin (n + 1)) : Fin (n + 1) →o Fin (n + 1) where
  toFun x := min x k
  monotone' _ _ h := min_le_min_right k h

/--
概要：元の頂点または k だけを使う写像のホモトピーは k-horn を保つ。
方針：入力の単体が欠く j≠k は、区間の各段階でも現れない。
規約：Segal 1974 Proposition 1.6 の引き戻し比較の補助。
使われ方：二つの収縮を horn 上に制限する。
-/
theorem simplexOrderHomotopyMap_mem_horn {n : ℕ} (k : Fin (n + 1))
    (f g : Fin (n + 1) →o Fin (n + 1)) (hfg : f ≤ g)
    (hf : ∀ x, f x = x ∨ f x = k) (hg : ∀ x, g x = x ∨ g x = k)
    (d : SimplexCategoryᵒᵖ) (s : (Δ[n] : SSet.{u}).obj d) (hs : s ∈ (Λ[n, k]).obj d)
    (t : (Δ[1] : SSet.{u}).obj d) :
    (simplexOrderHomotopyMap f g hfg).app d (s, t) ∈ (Λ[n, k]).obj d := by
  rw [SSet.mem_horn_iff_notMem_range] at hs ⊢
  obtain ⟨j, hj, hjs⟩ := hs
  refine ⟨j, hj, ?_⟩
  rintro ⟨i, hi⟩
  change (if SSet.stdSimplex.asOrderHom t i = 0 then
    f (SSet.stdSimplex.asOrderHom s i) else g (SSet.stdSimplex.asOrderHom s i)) = j at hi
  split_ifs at hi
  · rcases hf (SSet.stdSimplex.asOrderHom s i) with h | h
    · exact hjs ⟨i, h.symm.trans hi⟩
    · exact hj (hi.symm.trans h)
  · rcases hg (SSet.stdSimplex.asOrderHom s i) with h | h
    · exact hjs ⟨i, h.symm.trans hi⟩
    · exact hj (hi.symm.trans h)

/--
概要：min(x,k) から恒等写像へのホモトピー。
方針：min(x,k)≤x に単調写像のホモトピーを適用する。
規約：Segal 1974 Proposition 1.6 の同時収縮の第一段階。
使われ方：Kan fibration に沿う持ち上げの終点を指定する。
-/
def simplexMeetToIdentity {n : ℕ} (k : Fin (n + 1)) :
    SSet.Homotopy (simplexOrderMap (vertexMeet k)) (𝟙 (Δ[n] : SSet.{u})) :=
  { h := simplexOrderHomotopyMap (vertexMeet k) OrderHom.id (fun x => min_le_left x k)
    h₀ := (simplexOrderHomotopy (vertexMeet k) OrderHom.id (fun x => min_le_left x k)).h₀
    h₁ := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro s
      apply SSet.stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      rfl
    rel := (simplexOrderHomotopy (vertexMeet k) OrderHom.id (fun x => min_le_left x k)).rel }

/--
概要：min(x,k) から k への定数写像へのホモトピー。
方針：min(x,k)≤k に単調写像のホモトピーを適用する。
規約：Segal 1974 Proposition 1.6 の同時収縮の第二段階。
使われ方：終点を k 上のファイバーに移す。
-/
def simplexMeetToVertex {n : ℕ} (k : Fin (n + 1)) :
    SSet.Homotopy (simplexOrderMap (vertexMeet k))
      (SSet.const (X := (Δ[n] : SSet.{u})) (SSet.stdSimplex.obj₀Equiv.symm k)) :=
  simplexOrderHomotopy (vertexMeet k) (OrderHom.const _ k) (fun x => min_le_right x k)

/--
概要：第一の収縮は k-horn を保つ。
方針：最小値は元の値または k である。
規約：Segal 1974 Proposition 1.6 の組合せ的補助。
使われ方：horn の逆像上でのホモトピーの制限。
-/
theorem simplexMeetToIdentity_mem_horn {n : ℕ} (k : Fin (n + 1))
    (d : SimplexCategoryᵒᵖ) (s : (Δ[n] : SSet.{u}).obj d) (hs : s ∈ (Λ[n, k]).obj d)
    (t : (Δ[1] : SSet.{u}).obj d) :
    (simplexMeetToIdentity k).h.app d (s, t) ∈ (Λ[n, k]).obj d :=
  simplexOrderHomotopyMap_mem_horn k (vertexMeet k) OrderHom.id
    (fun x => min_le_left x k) (fun x => min_choice x k) (fun _ => Or.inl rfl)
    d s hs t

/--
概要：第二の収縮も k-horn を保つ。
方針：最小値と定数 k は入力以外の頂点を k しか作らない。
規約：Segal 1974 Proposition 1.6 の組合せ的補助。
使われ方：horn の逆像へ入る最終比較。
-/
theorem simplexMeetToVertex_mem_horn {n : ℕ} (k : Fin (n + 1))
    (d : SimplexCategoryᵒᵖ) (s : (Δ[n] : SSet.{u}).obj d) (hs : s ∈ (Λ[n, k]).obj d)
    (t : (Δ[1] : SSet.{u}).obj d) :
    (simplexMeetToVertex k).h.app d (s, t) ∈ (Λ[n, k]).obj d :=
  simplexOrderHomotopyMap_mem_horn k (vertexMeet k) (OrderHom.const _ k)
    (fun x => min_le_right x k) (fun x => min_choice x k) (fun _ => Or.inr rfl)
    d s hs t

end SerrePositivity.KST.Comparison
