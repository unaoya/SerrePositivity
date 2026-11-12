module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionCut

/-!
# 細分上の拡張退化作用素

概要：通常の退化を頂点 k+1 で拡張した Moss の r_n^k を構成する。
方針：退化写像による像に、必要な場合だけ初期区間 [0,k] を加える。
規約：Moss 2020 Definition 25、Lemma 26 (1)。Segal 1974 Proposition 1.6 の補助。
使われ方：Ex の単体の regular pairing の対応先を作る。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder

/--
概要：標準的な退化写像を ULift した頂点の単調写像。
方針：単体圏の σ^k を各頂点に適用する。
規約：Moss 2020 Definition 25 の通常の退化部分。
使われ方：非空有限集合の像を取る。
-/
def liftedDegeneracy (n : ℕ) (k : Fin (n + 1)) :
    ULift.{u} (Fin (n + 2)) →o ULift.{u} (Fin (n + 1)) where
  toFun x := ULift.up ((SimplexCategory.σ k) x.down)
  monotone' _ _ h := (SimplexCategory.σ k).toOrderHom.monotone h

/--
概要：標準的な余面を ULift した頂点の単調写像。
方針：単体圏の δ^i を各頂点に適用する。
規約：Moss 2020 Lemma 26 の作用素の比較。
使われ方：r_n^k の指定した面の計算。
-/
def liftedFace (n : ℕ) (i : Fin (n + 2)) :
    ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin (n + 2)) where
  toFun x := ULift.up ((SimplexCategory.δ i) x.down)
  monotone' _ _ h := (SimplexCategory.δ i).toOrderHom.monotone h

/--
概要：有限鎖の像に、頂点 k+1 を含むときだけ初期区間 [0,k] を加える。
方針：通常の退化による像は常に非空であり、加える区間も単調に動く。
規約：Moss 2020 Definition 25 の r_n^k の頂点上の式。
使われ方：細分の拡張退化作用素。
-/
def finiteChainDegeneracy (n : ℕ) (k : Fin (n + 1)) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 2))) →o
      NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  toFun s :=
    if ULift.up k.succ ∈ s.finset then
      { finset := (s.map (liftedDegeneracy n k)).finset ∪
          (finiteChainInitialSegment n (ULift.up k)).finset
        nonempty := (s.map (liftedDegeneracy n k)).nonempty.mono Finset.subset_union_left
        comparable a b := le_total a.val b.val }
    else s.map (liftedDegeneracy n k)
  monotone' a b hab := by
    have hm := (NonemptyFiniteChains.orderHomMap (liftedDegeneracy n k)).monotone hab
    by_cases ha : ULift.up k.succ ∈ a.finset
    · have hb : ULift.up k.succ ∈ b.finset := hab ha
      simp only [ha, hb, ↓reduceIte]
      exact Finset.union_subset_union hm le_rfl
    · by_cases hb : ULift.up k.succ ∈ b.finset
      · simp only [ha, hb, ↓reduceIte]
        exact hm.trans Finset.subset_union_left
      · simp only [ha, hb, ↓reduceIte]
        exact hm

/--
概要：指定した余面の像は拡張退化で特別扱いする頂点を含まない。
方針：δ^{k+1} の像から k+1 は除かれている。
規約：Moss 2020 Lemma 26 (1) の補助。
使われ方：初期区間を加えない場合への還元。
-/
theorem liftedFace_image_not_mem (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    ULift.up k.succ ∉ (s.map (liftedFace n k.succ)).finset := by
  intro h
  obtain ⟨x, _, hx⟩ := (NonemptyFiniteChains.mem_map_iff s (liftedFace n k.succ) _).mp h
  have h' := congrArg ULift.down hx
  exact Fin.succAbove_ne k.succ x.down h'

/--
概要：指定した余面の後に拡張退化を適用すると元の有限鎖に戻る。
方針：特別な頂点を含まないので通常の δ^{k+1} と σ^k の合成へ帰着する。
規約：Moss 2020 Lemma 26 (1)。
使われ方：pairing の対応先の指定した面が元の単体となること。
-/
theorem finiteChainDegeneracy_face (n : ℕ) (k : Fin (n + 1))
    (s : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    finiteChainDegeneracy n k (s.map (liftedFace n k.succ)) = s := by
  change (if ULift.up k.succ ∈ (s.map (liftedFace n k.succ)).finset then _ else _) = s
  rw [ite_eq_right (liftedFace_image_not_mem n k s)]
  apply NonemptyFiniteChains.ext
  ext x
  simp only [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
    have h : liftedDegeneracy n k (liftedFace n k.succ z) = z := by
      apply ULift.ext
      exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f z.down)
        SimplexCategory.δ_comp_σ_succ
    rw [h] at hzx
    exact hzx ▸ hz
  · intro hx
    refine ⟨liftedFace n k.succ x, ⟨x, hx, rfl⟩, ?_⟩
    apply ULift.ext
    exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f x.down)
      SimplexCategory.δ_comp_σ_succ

/--
概要：Moss の拡張退化写像 r_n^k。
方針：有限鎖上の単調写像に nerve を適用する。
規約：Moss 2020 Definition 25。
使われ方：Ex の regular pairing で加える高次単体の構成。
-/
def subdivisionDegeneracyAt (n : ℕ) (k : Fin (n + 1)) :
    SimplexCategory.sd.{u}.obj (SimplexCategory.mk (n + 1)) ⟶
      SimplexCategory.sd.obj (SimplexCategory.mk n) :=
  nerveMap (finiteChainDegeneracy n k).monotone.functor

/--
概要：拡張退化の指定した面は恒等射である。
方針：nerve の各頂点で有限鎖の式を使う。
規約：Moss 2020 Lemma 26 (1)。
使われ方：pairing の一方が他方の面であること。
-/
@[reassoc] theorem subdivisionDegeneracyAt_face (n : ℕ) (k : Fin (n + 1)) :
    SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ subdivisionDegeneracyAt.{u} n k = 𝟙 _ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  exact finiteChainDegeneracy_face n k (s.obj i)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
