module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveSimplexEndpoint
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Elements
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 中断した任意モデル源への一般化：NerveCoherentFamily

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Coherent families with values at the changing endpoint of a chain。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0466][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0466
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coherent families with values at the changing endpoint of a chain

All simplex operators act in the actual simplex category of the nerve.
The last face uses the value diagram's actual tail map. The index has a
Reedy structure even when the original category has large objects.
No model structure, smallness or functorial source factorization is used.
-/

@[expose] public section
universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.NerveSimplexEndpoint

namespace SerrePositivity.SimplicialModel.NerveCoherentFamily
variable (D : Type u) [Category.{v} D]

abbrev inverse : MorphismProperty (Index D) :=
  (Reedy.elementsDirect (direct := Reedy.simplexInverse.op) (nerve D)).op
abbrev direct : MorphismProperty (Index D) :=
  (Reedy.elementsInverse (inverse := Reedy.simplexDirect.op) (nerve D)).op

/-- The actual simplex category of the nerve, with its lifted Reedy structure. -/
abbrev reedy : ReedyStructure (inverse D) (direct D) ℕ :=
  (Reedy.elementsReedy (nerve D) Reedy.simplexOp).op

lemma reedy_degree (s : Index D) : (reedy D).deg s = dimension s := rfl

/-- Small simplices, even though their category of labels can have large objects. -/
def simplices : Index D ⥤ SSet.{w} where
  obj s := SSet.stdSimplex.obj (SimplexCategory.mk (dimension s))
  map f := SSet.stdSimplex.map (operator f)
  map_id _ :=  SSet.stdSimplex.map_id _
  map_comp _ _ := SSet.stdSimplex.map_comp _ _

variable {D}

lemma operator_epi {s t : Index D} (f : s ⟶ t) (hf : inverse D f) : Epi (operator f) := hf

lemma operator_last {s t : Index D} (f : s ⟶ t) (hf : inverse D f) :
    (operator f).toOrderHom (Fin.last (dimension s)) = Fin.last (dimension t) := by
  have : Epi (operator f) := operator_epi f hf
  obtain ⟨i, hi⟩ := (SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi (operator f)))
    (Fin.last (dimension t))
  apply le_antisymm (Fin.le_last _)
  rw [← hi]
  exact (operator f).toOrderHom.monotone (Fin.le_last i)

/-- Degeneracies change the endpoint only by its canonical equality isomorphism. -/
lemma endpointMap_isIso {s t : Index D} (f : s ⟶ t) (hf : inverse D f) :
    IsIso ((NerveSimplexEndpoint.functor D).map f) := by
  have hlast := operator_last f hf
  have hm : homOfLE (Fin.le_last ((operator f).toOrderHom (Fin.last (dimension s)))) =
      eqToHom hlast := Subsingleton.elim _ _
  have : IsIso
      (homOfLE (Fin.le_last ((operator f).toOrderHom (Fin.last (dimension s))))) := by
    rw [hm]
    infer_instance
  dsimp [NerveSimplexEndpoint.functor, endpointMap, tail]
  infer_instance

variable (F : D ⥤ SSet.{w})

abbrev values : Index D ⥤ SSet.{w} := NerveSimplexEndpoint.functor D ⋙ F

/-- A family on every composable chain, respecting all faces and degeneracies. -/
abbrev System := simplices D ⟶ values F

lemma compatibility (a : System F) {s t : Index D} (f : s ⟶ t) :
    SSet.stdSimplex.map (operator f) ≫ a.app t =
      a.app s ≫ F.map (endpointMap f) := a.naturality f

lemma reindex_compatibility (a : System F) {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ a.app (ofChain c) =
      a.app (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
        F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) := by
  have h := compatibility F a (reindexArrow c θ)
  rw [reindexArrow_endpoint] at h
  exact h

/-- Collapse the parameter simplex while retaining its actual endpoint. -/
def collapse : simplices D ⟶ (Functor.const (Index D)).obj
    (SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0)) where
  app _ := SSet.stdSimplex.isTerminalObj₀.from _
  naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- A strictly natural point supplies a coherent baseline in every chain dimension. -/
def ofPoint (p : (Functor.const D).obj
    (SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0)) ⟶ F) : System F :=
  collapse (D := D) ≫ Functor.whiskerLeft (NerveSimplexEndpoint.functor D) p

lemma ofPoint_component (p : (Functor.const D).obj
    (SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0)) ⟶ F) (s : Index D) :
    (ofPoint F p).app s = SSet.stdSimplex.isTerminalObj₀.from _ ≫ p.app (endpoint s) := rfl

/-- A map of value diagrams transports the whole coherent family at once. -/
def map {G : D ⥤ SSet.{w}} (q : F ⟶ G) (a : System F) : System G :=
  a ≫ Functor.whiskerLeft (NerveSimplexEndpoint.functor D) q

end SerrePositivity.SimplicialModel.NerveCoherentFamily
