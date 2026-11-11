module

public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 離散単体的集合を値とするホモトピックな二射は等しい

## 概要
離散単体的集合を値とするホモトピックな二射は等しい。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0512][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0512
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17

対応節は Kerodon 1.1（Tag 0004）。
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Maps into discrete simplicial sets and connected components

These constructions are independent of any model structure on simplicial sets.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
variable {X : SSet.{v}} {T : Type v}

abbrev zero : SimplexCategoryᵒᵖ := op (SimplexCategory.mk 0)
@[kerodon 00FS, kerodon 00G1]
abbrev discrete (T : Type v) : SSet.{v} := (Functor.const SimplexCategoryᵒᵖ).obj T

abbrev vertex (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) : n ⟶ zero :=
  (SimplexCategory.const (SimplexCategory.mk 0) n.unop i).op

lemma vertex_zero_id : vertex zero 0 = 𝟙 zero := by
  apply Quiver.Hom.unop_inj
  ext i
  have hi := i.isLt
  change i.val < 1 at hi
  change 0 = i.val
  omega

lemma vertex_component (n : SimplexCategoryᵒᵖ) (x : X.obj n)
    (i : Fin (n.unop.len + 1)) :
    SSet.π₀.mk (X.map (vertex n 0) x) = SSet.π₀.mk (X.map (vertex n i) x) := by
  let e := SSet.stdSimplex.edge n.unop.len 0 i (Fin.zero_le i)
  let p := (SSet.Edge.mk' e).map (SSet.yonedaEquiv.symm x)
  convert SSet.π₀.sound p using 1
  · apply congrArg SSet.π₀.mk
    change X.map (vertex n 0) x = X.map _ x
    apply congrArg (fun θ => X.map θ x)
    apply Quiver.Hom.unop_inj
    ext j
    fin_cases j
    rfl
  · apply congrArg SSet.π₀.mk
    change X.map (vertex n i) x = X.map _ x
    apply congrArg (fun θ => X.map θ x)
    apply Quiver.Hom.unop_inj
    ext j
    fin_cases j
    rfl

@[kerodon 00GP]
def component (n : SimplexCategoryᵒᵖ) (x : X.obj n) : SSet.π₀ X :=
  SSet.π₀.mk (X.map (vertex n 0) x)

lemma component_zero (x : X.obj zero) : component zero x = SSet.π₀.mk x := by
  unfold component
  rw [vertex_zero_id, X.map_id]
  rfl

lemma component_operator {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : X.obj n) :
    component m (X.map θ x) = component n x := by
  unfold component
  rw [← ConcreteCategory.comp_apply, ← X.map_comp]
  exact (vertex_component n x (θ.unop.toOrderHom 0)).symm

@[kerodon 00GP]
def fromComponents (t : SSet.π₀ X → T) : X ⟶ discrete T where
  app n := ↾fun x => t (component n x)
  naturality {_ _} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg t (component_operator θ x)

lemma fromComponents_zero (t : SSet.π₀ X → T) (x : X.obj zero) :
    (fromComponents t).app zero x = t (SSet.π₀.mk x) := by
  change t (component zero x) = _
  rw [component_zero]

def toComponents (f : X ⟶ discrete T) : SSet.π₀ X → T :=
  SSet.π₀.lift (f.app zero) (fun {x y} e => by
    have h₀ := types_congr_hom (f.naturality (SimplexCategory.δ (1 : Fin 2)).op) e.edge
    have h₁ := types_congr_hom (f.naturality (SimplexCategory.δ (0 : Fin 2)).op) e.edge
    exact (congrArg (f.app zero) e.src_eq.symm).trans
      (h₀.trans (h₁.symm.trans (congrArg (f.app zero) e.tgt_eq))))

/-- 離散単体的集合への写像と連結成分からの関数との全単射を構成する。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
@[kerodon 00GQ]
def homEquiv : (X ⟶ discrete T) ≃ (SSet.π₀ X → T) where
  toFun := toComponents
  invFun := fromComponents
  left_inv f := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact types_congr_hom (f.naturality (vertex n 0)) x
  right_inv t := by
    funext z
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
    exact fromComponents_zero t x

lemma yoneda_face {n : ℕ} (f : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶
    discrete T) (j : Fin (n + 2)) :
    SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ f) = SSet.yonedaEquiv f := by
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp]
  rfl

lemma discrete_kan (T : Type v) : SSet.KanComplex (discrete T) := by
  apply SSet.KanComplex.iff.mpr
  intro n i f hf
  obtain ⟨j, hj⟩ := exists_ne i
  have he (k : Fin (n + 2)) (hk : k ≠ i) :
      SSet.yonedaEquiv (f j hj) = SSet.yonedaEquiv (f k hk) := by
    cases n with
    | zero =>
      have hkj : k = j := by fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
      subst k
      rfl
    | succ n =>
      rcases lt_trichotomy j k with hjk | hjk | hjk
      · have h := congrArg SSet.yonedaEquiv (hf j k hj hk hjk)
        simpa only [yoneda_face] using h
      · subst k
        rfl
      · have h := congrArg SSet.yonedaEquiv (hf k j hk hj hjk)
        symm
        simpa only [yoneda_face] using h
  let t : T := SSet.yonedaEquiv (f j hj)
  refine ⟨(SSet.yonedaEquiv (n := SimplexCategory.mk (n + 1))
    (X := discrete T)).symm t, fun k hk => ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [yoneda_face, Equiv.apply_symm_apply]
  exact he k hk

lemma discrete_terminal_rlp (T : Type v) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (discrete T)) := by
  have := discrete_kan T
  exact (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance

/-- 離散単体的集合を値とするホモトピックな二射は等しい。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
lemma homotopy_eq {f g : X ⟶ discrete T} (H : SSet.Homotopy f g) : f = g := by
  apply homEquiv.injective
  funext z
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective z
  have hf := types_congr_hom (H.toSimplicialObjectHomotopy.h_last_comp_δ_last 0) x
  have hg := types_congr_hom (H.toSimplicialObjectHomotopy.h_zero_comp_δ_zero 0) x
  change (f.app zero) x = (g.app zero) x
  exact hf.symm.trans hg

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
