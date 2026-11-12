module

public import SerrePositivity.KST.Comparison.PairContractionAnodyne
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 順序集合の nerve の部分対象を保つ収縮

概要：共通の上側の写像を経由する収縮から、順序集合の部分対象の nerve の anodyne 性を得る。
方針：比較可能な単調写像を区間で結び、向きを指定した二段階の収縮の補題を使う。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分された horn への補助。
使われ方：頂点を加える操作による面の部分順序集合の収縮。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory
open scoped _root_.Simplicial

/--
概要：順序集合の部分集合に全頂点が属する単体からなる部分単体集合。
方針：nerve の単体の対象写像に性質を課す。
規約：部分順序を継承した部分集合の nerve の像。
使われ方：部分集合を保つ区間写像の制限。
-/
def orderNerveSubcomplex {P : Type u} [PartialOrder P] (S : P → Prop) :
    (nerve P).Subcomplex where
  obj _ := {s | ∀ i, S (s.obj i)}
  map f _ hs := fun i => hs (f.unop i)

/--
概要：比較可能な二つの単調写像を区間の座標で選ぶ単調写像。
方針：零端点では下の写像を、一端点では上の写像を使う。
規約：単調性は二つの座標の単調性と点ごとの比較による。
使われ方：nerve 上の実ホモトピー。
-/
def orderIntervalMap {P : Type u} [PartialOrder P] (f g : P →o P) (hfg : f ≤ g) :
    P × Fin 2 →o P where
  toFun p := if p.2 = 0 then f p.1 else g p.1
  monotone' a b h := by
    by_cases ha : a.2 = 0
    · by_cases hb : b.2 = 0
      · simpa only [ha, hb, ↓reduceIte] using f.monotone h.1
      · simpa only [ha, hb, ↓reduceIte] using (hfg a.1).trans (g.monotone h.1)
    · have hb : b.2 ≠ 0 := by
        intro hb
        exact ha (le_antisymm (hb ▸ h.2) (Fin.zero_le _))
      simpa only [ha, hb, ↓reduceIte] using g.monotone h.1

/--
概要：比較可能な単調写像を結ぶ nerve 上の区間写像。
方針：単体の射列と区間の射列の直積に、区間の単調写像を合成する。
規約：両端点の写像はそれぞれ f と g の nerve。
使われ方：部分集合を保つ二段階の収縮。
-/
def orderNerveHomotopyMap {P : Type u} [PartialOrder P] (f g : P →o P) (hfg : f ≤ g) :
    nerve P ⊗ (Δ[1] : SSet.{u}) ⟶ nerve P where
  app d := ↾fun p =>
    let θ : Fin (d.unop.len + 1) →o P × Fin 2 :=
      { toFun i := (p.1.obj i, (SSet.stdSimplex.objEquiv p.2) i)
        monotone' i j h := ⟨leOfHom (p.1.map (homOfLE h)),
          (SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone h⟩ }
    ((orderIntervalMap f g hfg).comp θ).monotone.functor
  naturality := by
    intros
    apply ConcreteCategory.hom_ext
    intro p
    apply nerve.ext_of_isThin
    rfl

/--
概要：順序の区間写像の零端点は下側の単調写像の nerve である。
方針：薄い圏の関手を対象上で評価する。
規約：零端点では f を選ぶ。
使われ方：収縮の始点の式。
-/
theorem orderNerveHomotopyMap_zero {P : Type u} [PartialOrder P]
    (f g : P →o P) (hfg : f ≤ g) :
    SSet.ι₀ ≫ orderNerveHomotopyMap f g hfg = nerveMap f.monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

/--
概要：順序の区間写像の一端点は上側の単調写像の nerve である。
方針：薄い圏の関手を対象上で評価する。
規約：一端点では g を選ぶ。
使われ方：収縮の共通の終点の式。
-/
theorem orderNerveHomotopyMap_one {P : Type u} [PartialOrder P]
    (f g : P →o P) (hfg : f ≤ g) :
    SSet.ι₁ ≫ orderNerveHomotopyMap f g hfg = nerveMap g.monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

/--
概要：二つの単調写像が部分集合を保てば、その間の区間写像も nerve の部分対象を保つ。
方針：各頂点で二つの写像のどちらを使うかで場合分けする。
規約：部分集合について下方閉性を仮定しない。
使われ方：二段階の収縮の相対性。
-/
theorem orderNerveHomotopyMap_mem {P : Type u} [PartialOrder P]
    (S : P → Prop) (f g : P →o P) (hfg : f ≤ g)
    (hf : ∀ x, S x → S (f x)) (hg : ∀ x, S x → S (g x))
    (d : SimplexCategoryᵒᵖ) (a : (orderNerveSubcomplex S).obj d)
    (t : (Δ[1] : SSet.{u}).obj d) :
    (orderNerveHomotopyMap f g hfg).app d (a.val, t) ∈ (orderNerveSubcomplex S).obj d := by
  intro i
  change S (if (SSet.stdSimplex.objEquiv t) i = 0 then f (a.val.obj i) else g (a.val.obj i))
  split_ifs
  · exact hf _ (a.property i)
  · exact hg _ (a.property i)

/--
概要：恒等写像と部分集合内の定数を共通の上側の写像へ結べれば、nerve の包含は anodyne である。
方針：部分集合を保つ二つの順序の区間写像を、共通の終点を持つ収縮として使う。
規約：Moss 原論文 Proposition 2.19 の pairing とは異なる相対ホモトピーの証明。
使われ方：horn の安全な面に頂点を加える収縮。
-/
theorem orderNerveSubcomplex_anodyne {P : Type u} [PartialOrder P]
    (S : P → Prop) (p : P) (hp : S p) (g : P →o P)
    (hg : ∀ x, S x → S (g x)) (hId : ∀ x, x ≤ g x) (hP : ∀ x, p ≤ g x) :
    SSet.anodyneExtensions (orderNerveSubcomplex S).ι := by
  let f : P →o P := OrderHom.id
  let c : P →o P := OrderHom.const P p
  let H₀ := orderNerveHomotopyMap f g hId
  let H₁ := orderNerveHomotopyMap c g hP
  apply subcomplex_pairContraction_anodyne (orderNerveSubcomplex S) 1 0 H₀ H₁
  · rw [intervalEndpoint_one_eq, orderNerveHomotopyMap_zero]
    rfl
  · simp only [show (1 : Fin 2).rev = 0 by decide, intervalEndpoint_zero_eq,
      H₀, H₁, orderNerveHomotopyMap_one]
  · exact orderNerveHomotopyMap_mem S f g hId (fun _ h => h) hg
  · exact orderNerveHomotopyMap_mem S c g hP (fun _ _ => hp) hg
  · simp only [show (0 : Fin 2).rev = 1 by decide, intervalEndpoint_one_eq,
      H₁, orderNerveHomotopyMap_zero]
    rintro d s ⟨a, rfl⟩ i
    exact hp

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
