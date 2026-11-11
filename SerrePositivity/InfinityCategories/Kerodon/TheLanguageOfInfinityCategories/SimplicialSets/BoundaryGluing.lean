module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# 互換な標準面の族を実際の単体境界上の一つの射に貼り合わせる

## 概要
互換な標準面の族を実際の単体境界上の一つの射に貼り合わせる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0354][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0354
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17

対応節は Kerodon 1.1（Tag 0004）。
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing prescribed simplicial faces from their actual intersections

The boundary map is constructed from a compatible family of facet maps.
Compatibility on actual subcomplex intersections is retained, so previously
chosen lower-dimensional comparisons can be prescribed before filling.
The construction is model independent and also works in dimension zero.
-/

@[expose] public section
universe v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
variable {X P : SSet.{v}} {I : Type w} (A : X.Subcomplex) (U : I → X.Subcomplex)
  (hU : ⨆ i, U i = A)

abbrev _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.diagram : SSet.Subcomplex.MulticoequalizerDiagram A U (fun i j => U i ⊓ U j) :=
  ⟨hU, fun _ _ => rfl⟩

def _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.SubcomplexGluing.desc (f : ∀ i, (U i).toSSet ⟶ P)
    (hf : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      SSet.Subcomplex.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) : A.toSSet ⟶ P :=
  Multicofork.IsColimit.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.diagram A U hU).isColimit f (fun ij => hf ij.1 ij.2)

@[reassoc]
lemma _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.SubcomplexGluing.desc_fac (f : ∀ i, (U i).toSSet ⟶ P)
    (hf : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      SSet.Subcomplex.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i : I) :
    SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.SubcomplexGluing.desc A U hU f hf = f i :=
  Multicofork.IsColimit.fac (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.diagram A U hU).isColimit f (fun ij => hf ij.1 ij.2) i

lemma _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.hom_ext {f g : A.toSSet ⟶ P}
    (h : ∀ i, SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ f =
      SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ g) : f = g :=
  Multicofork.IsColimit.hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.diagram A U hU).isColimit h

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing

abbrev facet (n : ℕ) (i : Fin (n + 1)) :
    (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n)).Subcomplex :=
  SSet.stdSimplex.face {i}ᶜ

abbrev Compatible {P : SSet.{v}} {n : ℕ} (f : ∀ i, (facet n i).toSSet ⟶ P) : Prop :=
  ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : facet n i ⊓ facet n j ≤ facet n i) ≫ f i =
    SSet.Subcomplex.homOfLE (inf_le_right : facet n i ⊓ facet n j ≤ facet n j) ≫ f j

def _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.BoundaryGluing.desc {P : SSet.{v}} {n : ℕ} (f : ∀ i, (facet n i).toSSet ⟶ P) (hf : Compatible f) :
    (SSet.boundary.{v} n).toSSet ⟶ P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.SubcomplexGluing.desc (SSet.boundary n) (facet n) (SSet.boundary_eq_iSup n).symm f hf

@[reassoc]
lemma _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.BoundaryGluing.desc_fac {P : SSet.{v}} {n : ℕ} (f : ∀ i, (facet n i).toSSet ⟶ P) (hf : Compatible f)
    (i : Fin (n + 1)) : SSet.boundary.faceι i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.BoundaryGluing.desc f hf = f i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.SubcomplexGluing.desc_fac (SSet.boundary n) (facet n) (SSet.boundary_eq_iSup n).symm f hf i

abbrev standardDiagram (n : ℕ) : SSet.Subcomplex.MulticoequalizerDiagram (SSet.boundary.{v} n)
    (facet n) (fun i j => SSet.stdSimplex.face {i, j}ᶜ) where
  iSup_eq := (SSet.boundary_eq_iSup n).symm
  eq_inf i j := by
    rw [SSet.stdSimplex.face_inter_face]
    congr
    aesop

/-- The usual face identities, for a boundary in dimension at least two. -/
abbrev StandardCompatible {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P)) : Prop :=
  ∀ (j k : Fin (n + 3)) (hjk : j < k),
    SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
      SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k

/-- The faces of an actual boundary map satisfy all ordinary face identities. -/
lemma standardCompatible_of_boundary {P : SSet.{v}} {n : ℕ}
    (q : (SSet.boundary.{v} (n + 2)).toSSet ⟶ P) :
    StandardCompatible (fun k => SSet.boundary.ι k ≫ q) := by
  intro j k hjk
  have h :
      SSet.stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ SSet.boundary.ι j =
        SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ SSet.boundary.ι k := by
    apply (cancel_mono (SSet.boundary.{v} (n + 2)).ι).mp
    simpa only [Category.assoc, SSet.boundary.ι_ι] using
      (SSet.stdSimplex.facePairComplIso_hom_ι' j k hjk).symm.trans
        (SSet.stdSimplex.facePairComplIso_hom_ι j k hjk)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ q) h).trans (Category.assoc _ _ _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
def standardCofork {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : StandardCompatible f) :
    Multicofork ((standardDiagram.{v} (n + 2)).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ P (fun j => (SSet.stdSimplex.faceSingletonComplIso j).inv ≫ f j) (by
    rintro ⟨⟨j, k⟩, hjk : j < k⟩
    dsimp
    rw [SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc
      _ _ hjk,
      SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc
        _ _ hjk, hf j k hjk])

/-- 互換な標準面の族を実際の単体境界上の一つの射に貼り合わせる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
def standardDesc {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : StandardCompatible f) : (SSet.boundary.{v} (n + 2)).toSSet ⟶ P :=
  ((standardDiagram.{v} (n + 2)).isColimit').desc (standardCofork f hf)

set_option backward.isDefEq.respectTransparency.types false in
/-- 境界へ貼り合わせた射の各標準面への制限は指定した面そのものとなる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
構成に現れる射と比較写像を明示し、各成分の等式を照合する。
既存の普遍性と自然性、必要な帰納を用いて全体の主張へ接続する。
-/
@[reassoc]
lemma standardDesc_fac {P : SSet.{v}} {n : ℕ}
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ P))
    (hf : StandardCompatible f) (k : Fin (n + 3)) :
    SSet.boundary.ι k ≫ standardDesc f hf = f k := by
  rw [← cancel_epi (SSet.stdSimplex.faceSingletonComplIso k).inv]
  simpa [standardDesc, standardCofork] using!
    ((standardDiagram.{v} (n + 2)).isColimit').fac (standardCofork f hf) (.right k)

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing
