module

public import Mathlib.CategoryTheory.Limits.Final
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.CofibrantBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsMatchingEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalMatching
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexIndexFinite
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalMatching

/-!
# 単体圏上のパラメータ図式のlatching射を実際の単体境界射と同型で結ぶ

## 概要
単体圏上のパラメータ図式のlatching射を実際の単体境界射と同型で結ぶ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0559][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0559
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual latching boundaries of simplex parameters on a large simplex category

The projection identifies the whole direct boundary diagram with the
ordinary simplex boundary diagram. Its actual colimit and comparison map
are the standard boundary and boundary inclusion, in an independent value
universe. No smallness of the original simplex category is assumed.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.SimplexLatchingBoundary
variable (X : SSet.{w}) (s : X.Elementsᵒᵖ)

abbrev degree (s : X.Elementsᵒᵖ) := s.unop.obj.unop

def projection : X.Elementsᵒᵖ ⥤ SimplexCategory where
  obj := degree X
  map f := f.unop.hom.unop

abbrev parameters : X.Elementsᵒᵖ ⥤ SSet.{v} := projection X ⋙ SSet.stdSimplex

lemma projection_identities {a b : X.Elementsᵒᵖ} (f : a ⟶ b)
    (h : MorphismProperty.identities X.Elementsᵒᵖ f) :
    MorphismProperty.identities SimplexCategory f.unop.hom.unop := by
  cases h
  exact (MorphismProperty.identities SimplexCategory).id_mem _

abbrev code (q : LatchingIndex (SimplexIndexFinite.reedy X) s) :
    LatchingIndex simplex (degree X s) :=
  ⟨Over.mk q.obj.hom.unop.hom.unop, q.property.1, fun h => q.property.2
    ((MorphismProperty.identities_op_iff _).2 (elements_identities X q.obj.hom.unop
      ((MorphismProperty.identities_op_iff _).2 h)))⟩

def forget : LatchingIndex (SimplexIndexFinite.reedy X) s ⥤
    LatchingIndex simplex (degree X s) where
  obj := code X s
  map φ := ObjectProperty.homMk (Over.homMk φ.hom.left.unop.hom.unop
    (congrArg (fun f => f.unop.hom.unop) (Over.w φ.hom)))

def fullyFaithful : (forget X s).FullyFaithful where
  preimage φ := elementsLatchingOpPreimage X simplexOp s.unop
    (ObjectProperty.homMk (Over.homMk φ.hom.left.op.op
      (congrArg (fun f => f.op.op) (Over.w φ.hom))))
  map_preimage φ := by
    apply ObjectProperty.hom_ext
    exact Over.OverMorphism.ext rfl
  preimage_map φ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Quiver.Hom.unop_inj
    exact Functor.Elements.hom_ext rfl

abbrev lift (q : LatchingIndex simplex (degree X s)) :
    LatchingIndex (SimplexIndexFinite.reedy X) s :=
  ⟨Over.mk (Functor.Elements.homMk
    (y := X.elementsMk (Opposite.op q.obj.left) (X.map q.obj.hom.op s.unop.val))
    q.obj.hom.op rfl).op, q.property.1,
    fun h => q.property.2 (projection_identities X _ h)⟩

lemma lift_code (q : LatchingIndex simplex (degree X s)) : code X s (lift X s q) = q := by
  rcases q with ⟨q, hq⟩
  obtain ⟨y, f, rfl⟩ := Over.mk_surjective q
  rfl

instance forget_full : (forget X s).Full := (fullyFaithful X s).full
instance forget_faithful : (forget X s).Faithful := (fullyFaithful X s).faithful
instance forget_essSurj : (forget X s).EssSurj where
  mem_essImage q := ⟨lift X s q, ⟨eqToIso (lift_code X s q)⟩⟩
instance forget_isEquivalence : (forget X s).IsEquivalence where

abbrev equivalence : LatchingIndex (SimplexIndexFinite.reedy X) s ≌
    LatchingIndex simplex (degree X s) := (forget X s).asEquivalence

lemma source_eq : forget X s ⋙ latchingSource simplex (degree X s) =
    latchingSource (SimplexIndexFinite.reedy X) s ⋙ projection X := rfl

/-- The actual small latching colimit on the possibly large simplex category. -/
def boundaryIso : (latchingEvaluation (SimplexIndexFinite.reedy X) s).obj (parameters.{w, v} X) ≅
    (SSet.boundary.{v} (degree X s).len).toSSet :=
  asIso (colimit.pre (latchingSource simplex (degree X s) ⋙ SSet.stdSimplex.{v}) (forget X s)) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso (degree X s).len

@[reassoc]
lemma boundaryIso_fac : (boundaryIso.{w, v} X s).hom ≫ (SSet.boundary.{v} (degree X s).len).ι =
    (latchingComparison (SimplexIndexFinite.reedy X) s).app (parameters.{w, v} X) := by
  apply colimit.hom_ext
  intro q
  change colimit.ι (forget X s ⋙
      (latchingSource simplex (degree X s) ⋙ SSet.stdSimplex.{v})) q ≫
      (colimit.pre (latchingSource simplex (degree X s) ⋙ SSet.stdSimplex.{v}) (forget X s) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso (degree X s).len).hom ≫
          (SSet.boundary.{v} (degree X s).len).ι) =
    colimit.ι (latchingSource (SimplexIndexFinite.reedy X) s ⋙ parameters.{w, v} X) q ≫
      colimit.desc _ (latchingCocone (SimplexIndexFinite.reedy X) (parameters.{w, v} X) s)
  rw [← Category.assoc, colimit.ι_pre,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.standardBoundaryIso_fac]
  change colimit.ι (latchingSource simplex (degree X s) ⋙ SSet.stdSimplex.{v})
      ((forget X s).obj q) ≫
      colimit.desc _ (latchingCocone simplex SSet.stdSimplex.{v} (degree X s)) = _
  rw [colimit.ι_desc, colimit.ι_desc]
  rfl

/- 旧宣言の技術注記：
The latching map and standard boundary inclusion are isomorphic as actual arrows.
-/
/-- 単体圏上のパラメータ図式のlatching射を実際の単体境界射と同型で結ぶ。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def boundaryArrowIso :
    Arrow.mk ((latchingComparison (SimplexIndexFinite.reedy X) s).app (parameters.{w, v} X)) ≅
      Arrow.mk (SSet.boundary.{v} (degree X s).len).ι :=
  Arrow.isoMk (boundaryIso.{w, v} X s) (Iso.refl _) (by
    exact (boundaryIso_fac X s).trans (Category.comp_id _).symm)

lemma latching_mono :
    Mono ((latchingComparison (SimplexIndexFinite.reedy X) s).app (parameters.{w, v} X)) := by
  rw [← boundaryIso_fac]
  infer_instance

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma reedy_cofibrant : reedyLeft (SimplexIndexFinite.reedy X) (cofibrations SSet.{v})
    (initial.to (parameters.{w, v} X)) := by
  intro s
  apply ((cofibrations SSet.{v}).arrow_iso_iff
    (latchingInitialArrowIso (SimplexIndexFinite.reedy X) s (parameters.{w, v} X))).mp
  rw [hcof]
  exact latching_mono X s

end SerrePositivity.SimplicialModel.SimplexLatchingBoundary
