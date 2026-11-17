module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinement
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowFaces

/-!
概要：実細分の挿入した頂点を除く指定面は、元の実全鎖へ戻る。
方針：先頭と尾部の実再帰、二つの射の面、対象の等式の輸送を照合する。
規約：元の辺が指定の二つの射の合成である場合に全関手の等式を証明する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の指定面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の面の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：先頭の辺の実細分は二回の先頭への挿入。
方針：実再帰の定義を照合する。規約：全関手の等式。
使われ方：Riehl–Verity §4.1の指定面の基底。 -/
lemma composableArrowRefinement_zero {n : ℕ} (F : ComposableArrows C (n + 1))
    (B : C) (q : F.obj (0 : Fin (n + 1)).castSucc ⟶ B)
    (g : B ⟶ F.obj (0 : Fin (n + 1)).succ) :
    composableArrowRefinement F 0 B q g = (F.δ₀.precomp g).precomp q := by
  cases n <;> rfl

/-- 概要：先頭以外の辺の実細分は尾部の細分へ元の先頭を戻したもの。
方針：実再帰の定義と両端の対象の証明非依存性を使う。規約：対象の輸送を保持する。
使われ方：Riehl–Verity §4.1の指定面の再帰。 -/
lemma composableArrowRefinement_succ {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) (B : C) (q : F.obj k.succ.castSucc ⟶ B)
    (g : B ⟶ F.obj k.succ.succ) :
    composableArrowRefinement F k.succ B q g =
      (composableArrowRefinement F.δ₀ k B q g).precomp
        (F.map' 0 1 ≫ eqToHom (composableArrowRefinement_first F.δ₀ k B q g).symm) := by
  rfl

/-- 概要：元の尾部へ最初の実射を挿入すると元の実全鎖。
方針：始点・尾部・最初の射を実表示で照合する。規約：全射を含む等式。
使われ方：Riehl–Verity §4.1の指定面からの元の全鎖の回収。 -/
lemma composableArrowPrecomp_decompose {n : ℕ} (F : ComposableArrows C (n + 1)) :
    F.δ₀.precomp (F.map' 0 1) = F := by
  apply ComposableArrows.ext_succ (F := F.δ₀.precomp (F.map' 0 1)) (G := F) rfl rfl
  simp [ComposableArrows.precomp, ComposableArrows.Precomp.map]
  rfl

/-- 概要：実全鎖の等式に沿う先頭の対象の輸送は先頭への挿入と両立する。
方針：二つの実関手を同一視する。規約：先頭の等式の証明も保持する。
使われ方：Riehl–Verity §4.1の指定面の再帰の貼り合わせ。 -/
lemma composableArrowPrecomp_transport {n : ℕ} {R S : ComposableArrows C n} (h : R = S)
    {A : C} (f : A ⟶ S.left) (h0 : R.left = S.left) :
    R.precomp (f ≫ eqToHom h0.symm) = S.precomp f := by
  subst S
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：細分した実全鎖の挿入頂点を除く面は元の全鎖。
方針：指定辺の位置で再帰し、面と先頭への挿入の全合成則を適用する。
規約：元の全辺の合成の等式だけを入力にする。使われ方：Riehl–Verity §4.1の指定面。 -/
lemma composableArrowRefinement_face :
    ∀ (n : ℕ) (F : ComposableArrows C (n + 1)) (k : Fin (n + 1))
      (B : C) (q : F.obj k.castSucc ⟶ B) (g : B ⟶ F.obj k.succ),
      q ≫ g = F.map (homOfLE (Fin.castSucc_le_succ k)) →
        finiteChainFace (composableArrowRefinement F k B q g) k.succ.castSucc = F := by
  intro n
  induction n with
  | zero =>
    intro F k B q g fac
    have hk : k = 0 := by apply Fin.ext; have hi := k.isLt; change k.val = 0; omega
    subst k
    rw [composableArrowRefinement_zero]
    change finiteChainFace ((F.δ₀.precomp g).precomp q) (1 : Fin 3) = F
    rw [finiteChainFace_precomp_pair, fac]
    exact composableArrowPrecomp_decompose F
  | succ n ih =>
    intro F k
    refine Fin.cases ?_ (fun k => ?_) k
    · intro B q g fac
      rw [composableArrowRefinement_zero]
      have hx : (0 : Fin (n + 2)).succ.castSucc = (1 : Fin (n + 4)) := by
        apply Fin.ext
        simp
      rw [hx, finiteChainFace_precomp_pair, fac]
      exact composableArrowPrecomp_decompose F
    · intro B q g fac
      let R := composableArrowRefinement F.δ₀ k B q g
      have hi : finiteChainFace R k.succ.castSucc = F.δ₀ := ih F.δ₀ k B q g fac
      have h0 : (finiteChainFace R k.succ.castSucc).left = F.δ₀.left :=
        congrArg (fun H : ComposableArrows C (n + 1) => H.left) hi
      erw [composableArrowRefinement_succ]
      change finiteChainFace (R.precomp
        (F.map' 0 1 ≫ eqToHom (composableArrowRefinement_first F.δ₀ k B q g).symm))
        k.castSucc.succ.succ = F
      rw [finiteChainFace_precomp_succ]
      change (finiteChainFace R k.succ.castSucc).precomp
        ((F.map' 0 1 ≫ eqToHom (composableArrowRefinement_first F.δ₀ k B q g).symm) ≫
          eqToHom (finiteChainFace_first R k.castSucc).symm) = F
      have hw :
          (F.map' 0 1 ≫ eqToHom (composableArrowRefinement_first F.δ₀ k B q g).symm) ≫
              eqToHom (finiteChainFace_first R k.castSucc).symm =
            F.map' 0 1 ≫ eqToHom h0.symm := by
        simp only [Category.assoc, eqToHom_trans]
      rw [hw]
      exact (composableArrowPrecomp_transport hi (F.map' 0 1) h0).trans
        (composableArrowPrecomp_decompose F)

end SerrePositivity.InfinityCategories.HA.Monads
