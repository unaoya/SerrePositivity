module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingParameter

/-!
# 中断した任意モデル源への一般化：NerveFirstChoice

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Coherent choices at the first endpoint for contravariant diagrams。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0473][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0473
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coherent choices at the first endpoint for contravariant diagrams

The first endpoint functor gives the actual prefix transport. All original
vertex points and arbitrary lower systems can be retained, without a model
structure on the value universe.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.NerveSimplexEndpoint SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.NerveFirstChoice
variable {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ SSet.{v})
  (hp : ∀ d, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (F.obj d))

abbrev values : Index D ⥤ SSet.{v} := NerveSimplexStart.functor D ⋙ F
abbrev System := NerveDiagramExtension.System (values F)
abbrev LowerSystem (n : ℕ) := NerveDiagramExtension.LowerSystem (values F) n
abbrev point : Index D ⥤ SSet.{v} := (Functor.const (Index D)).obj
  (SSet.stdSimplex.obj (SimplexCategory.mk 0))

def projection : values F ⟶ point (D := D) where
  app _ := SSet.stdSimplex.isTerminalObj₀.from _
  naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma inverts : NerveDiagramExtension.InvertsInverse (values F) := by
  intro s t f hf
  have := NerveBiparameter.startMap_isIso f hf
  exact Functor.map_isIso (F := F) (NerveSimplexStart.startMap f).op

lemma point_inverts : NerveDiagramExtension.InvertsInverse (point (D := D)) := by
  intro s t f _hf
  change IsIso (𝟙 _)
  infer_instance

include hp in
lemma rightLifting : ∀ s, (MorphismProperty.monomorphisms SSet.{v}).rlp
    ((projection F).app s) := fun s =>
  BoundaryFillerLifting.terminal_rightLifting (hp (Opposite.op (NerveSimplexStart.start s)))

lemma boundary (n : ℕ) (old : LowerSystem F n) : old ≫
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n) (projection F) =
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveCoherentFamily.collapse (D := D)) := by
  apply NatTrans.ext
  funext s
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

def extend (n : ℕ) (old : LowerSystem F n) : System F :=
  NerveDiagramExtension.extend (values F) (point (D := D)) (projection F)
    (inverts F) point_inverts (rightLifting F hp) (NerveCoherentFamily.collapse (D := D))
    n old (boundary F n old)

lemma extend_restrict (n : ℕ) (old : LowerSystem F n) :
    Functor.whiskerLeft (lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extend F hp n old) = old := NerveDiagramExtension.extend_restrict _ _ _ _ _ _ _ _ _ _

variable (points : ∀ d : D, SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj (Opposite.op d))

abbrev verticesApp (s : Lower (NerveCoherentFamily.reedy D) 1) :
    (NerveCoherentFamily.simplices D).obj s.obj ⟶ (values F).obj s.obj :=
  SSet.stdSimplex.isTerminalObj₀.from ((NerveCoherentFamily.simplices D).obj s.obj) ≫
    points (NerveSimplexStart.start s.obj)

def vertices : LowerSystem F 1 where
  app := verticesApp F points
  naturality {s t} f := naturality_on_lower_identities (NerveCoherentFamily.reedy D) 1
    (F := NerveCoherentFamily.simplices D) (G := values F)
    (verticesApp F points) f (RelativeLifting.degreeZero_identities
      (NerveCoherentFamily.reedy D) f.hom (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ s.property))
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ t.property)))

def extendVertices : System F := extend F hp 1 (vertices F points)

lemma extendVertices_point (d : D) :
    (extendVertices F hp points).app (ofChain (ComposableArrows.mk₀ d)) = points d := by
  have h := congr_app (extend_restrict F hp 1 (vertices F points))
    ⟨ofChain (ComposableArrows.mk₀ d), Nat.zero_lt_one⟩
  change _ = SSet.stdSimplex.isTerminalObj₀.from _ ≫ points d at h
  exact h.trans (by
    change SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ≫ points d = points d
    rw [show SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) = 𝟙 _ from
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _]
    exact Category.id_comp _)

lemma reindex_compatibility (a : System F) {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
      a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
        F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).op := by
  have h := a.naturality (reindexArrow c θ)
  change SSet.stdSimplex.map θ ≫ a.app (ofChain c) = _ at h
  rw [show (values F).map (reindexArrow c θ) =
    F.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))).op from
      by
        change F.map (NerveSimplexStart.startMap (reindexArrow c θ)).op = _
        rw [NerveSimplexStart.reindexArrow_start]] at h
  exact h

lemma constant (a : System F) (d : D) (n : ℕ) :
    a.app (ofChain ((Functor.const (Fin (n + 1))).obj d)) =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ a.app (ofChain (ComposableArrows.mk₀ d)) := by
  let θ : SimplexCategory.mk n ⟶ SimplexCategory.mk 0 := SimplexCategory.isTerminalZero.from _
  let a0 : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0) ⟶ F.obj (Opposite.op d) :=
    a.app (ofChain (ComposableArrows.mk₀ d))
  let an : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ F.obj (Opposite.op d) :=
    a.app (ofChain ((Functor.const (Fin (n + 1))).obj d))
  have h := reindex_compatibility F a (ComposableArrows.mk₀ d) θ
  change SSet.stdSimplex.map θ ≫ a0 = an ≫ F.map (𝟙 (Opposite.op d)) at h
  rw [F.map_id, Category.comp_id] at h
  change an = SSet.stdSimplex.isTerminalObj₀.from _ ≫ a0
  exact h.symm.trans (congrArg (fun k => k ≫ a0)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _))

end SerrePositivity.SimplicialModel.NerveFirstChoice
