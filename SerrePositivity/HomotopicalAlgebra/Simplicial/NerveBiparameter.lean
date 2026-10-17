module

public import SerrePositivity.CategoryTheory.NerveSimplexStart
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentFamily
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterMapping

/-!
# 中断した任意モデル源への一般化：NerveBiparameter

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Changing parameters at the first endpoint and values at the last endpoint。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0459][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0459
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Changing parameters at the first endpoint and values at the last endpoint

Every simplex operator transports the first parameter contravariantly and
the last value covariantly. Degeneracies are inverted by the actual maps.
-/

@[expose] public section
universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveBiparameter
variable {D : Type u} [Category.{v} D]

lemma operator_zero {s t : Index D} (f : s ⟶ t) (hf : NerveCoherentFamily.inverse D f) :
    (operator f).toOrderHom 0 = 0 := by
  have : Epi (operator f) := NerveCoherentFamily.operator_epi f hf
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi (operator f))) 0
  apply le_antisymm ?_ (Fin.zero_le _)
  rw [← hi]
  exact (operator f).toOrderHom.monotone (Fin.zero_le i)

lemma startMap_isIso {s t : Index D} (f : s ⟶ t) (hf : NerveCoherentFamily.inverse D f) :
    IsIso (NerveSimplexStart.startMap f) := by
  have hzero := operator_zero f hf
  have he : homOfLE (Fin.zero_le ((operator f).toOrderHom 0)) = eqToHom hzero.symm :=
    Subsingleton.elim _ _
  have : IsIso (homOfLE (Fin.zero_le ((operator f).toOrderHom 0))) := by
    rw [he]
    infer_instance
  dsimp [NerveSimplexStart.startMap, NerveSimplexStart.initialSegment]
  infer_instance

abbrev endpoints (D : Type u) [Category.{v} D] : Index D ⥤ Dᵒᵖ × D :=
  (NerveSimplexStart.functor D).prod' (NerveSimplexEndpoint.functor D)

/-- Whole moving parameter/value mapping spaces on the actual nerve simplex category. -/
abbrev values (K F : D ⥤ SSet.{w}) : Index D ⥤ SSet.{w} :=
  endpoints D ⋙ K.op.prod F ⋙ Functor.uncurry.obj MonoidalClosed.internalHom

abbrev System (K F : D ⥤ SSet.{w}) := NerveCoherentFamily.simplices D ⟶ values K F

lemma values_map_isIso (K F : D ⥤ SSet.{w}) {s t : Index D} (f : s ⟶ t)
    (hf : NerveCoherentFamily.inverse D f) : IsIso ((values K F).map f) := by
  have hs : IsIso (NerveSimplexStart.startMap f) := startMap_isIso f hf
  have ht : IsIso (endpointMap f) := NerveCoherentFamily.endpointMap_isIso f hf
  have hi : IsIso ((endpoints D).map f) := by
    change IsIso (show
      (Opposite.op (NerveSimplexStart.start s), endpoint s) ⟶
        (Opposite.op (NerveSimplexStart.start t), endpoint t) from
          ((NerveSimplexStart.startMap f).op, endpointMap f))
    exact (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  exact Functor.map_isIso (F := K.op.prod F ⋙
    Functor.uncurry.obj (MonoidalClosed.internalHom (C := SSet.{w}))) ((endpoints D).map f)


lemma compatibility (K F : D ⥤ SSet.{w}) (a : System K F) {s t : Index D} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ a.app t = a.app s ≫
      (pre (K.map (NerveSimplexStart.startMap f))).app (F.obj (endpoint s)) ≫
        (ihom (K.obj (NerveSimplexStart.start t))).map (F.map (endpointMap f)) := by
  exact a.naturality f

lemma reindex_compatibility (K F : D ⥤ SSet.{w}) (a : System K F) {n m : ℕ}
    (c : ComposableArrows D n) (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
      a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
        (pre (K.map (c.map (homOfLE (Fin.zero_le (θ.toOrderHom 0)))))).app
          (F.obj (c.obj (θ.toOrderHom (Fin.last m)))) ≫
        (ihom (K.obj (c.obj 0))).map
          (F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m)))))) := by
  have h := compatibility K F a (reindexArrow c θ)
  rw [NerveSimplexStart.reindexArrow_start, reindexArrow_endpoint] at h
  exact h

end SerrePositivity.SimplicialModel.NerveBiparameter
