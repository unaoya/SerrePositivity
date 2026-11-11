module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornSimplexFaceFactorization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFaceLifting

/-!
# horn の細分への余面の写像と共通の表示

概要：余面の面の nerve から horn の実際の細分への写像を扱う。
方針：標準細分同型を使い、共通の小さい面を経由する二つの射の一致を移す。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分比較の単射性への補助。
使われ方：二つの余面表示を共通の面から比較する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits
open scoped _root_.Simplicial

/--
概要：一つの余面の面の nerve から、horn の実際の細分への写像。
方針：標準細分同型の逆と、horn の余面の写像の細分を合成する。
規約：j は horn に許された、k と異なる余面の番号。
使われ方：horn の細分の各元の余面による表示。
-/
def hornSubdivisionFaceMap (n : ℕ) (k j : Fin (n + 2)) (hj : j ≠ k) :
    SimplexCategory.sd.{u}.obj ⦋n⦌ ⟶ SSet.sd.obj (SSet.horn.{u} (n + 1) k) :=
  SSet.stdSimplex.sdIso.inv.app ⦋n⦌ ≫ SSet.sd.map (SSet.horn.ι k j hj)

/--
概要：余面の面の nerve の写像を細分比較と包含で送ると、通常の細分された余面になる。
方針：既証の標準細分同型と余面の整合を使う。
規約：写像を短い名前で表した形。
使われ方：二つの余面表示の像の等式。
-/
@[reassoc] theorem hornSubdivisionFaceMap_ambient (n : ℕ) (k j : Fin (n + 2)) (hj : j ≠ k) :
    hornSubdivisionFaceMap.{u} n k j hj ≫ hornSubdivisionComparison (n + 1) k ≫
      nerveMap (hornFaceInclusion (n + 1) k).monotone.functor =
        SimplexCategory.sd.map (SimplexCategory.δ j) :=
  hornSubdivisionComparison_face n k j hj

/--
概要：horn の細分の任意の単体は、一つの余面の面の nerve からの像に入る。
方針：実際の標準単体の細分による被覆を標準細分同型で移す。
規約：原像は面の有限鎖の射列として与える。
使われ方：細分比較の単射性を二つの余面表示に帰着する。
-/
theorem hornSubdivisionNerveFaceCover (n : ℕ) (k : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) (s : (SSet.sd.obj (SSet.horn.{u} (n + 1) k)).obj d) :
    ∃ (j : Fin (n + 2)) (hj : j ≠ k) (t : (SimplexCategory.sd.{u}.obj ⦋n⦌).obj d),
      (hornSubdivisionFaceMap n k j hj).app d t = s := by
  obtain ⟨j, hj, t, ht⟩ := hornSubdivisionFaceCover n k d s
  refine ⟨j, hj, (SSet.stdSimplex.sdIso.hom.app ⦋n⦌).app d t, ?_⟩
  have h := ConcreteCategory.congr_hom
    (congr_app (SSet.stdSimplex.sdIso.hom_inv_id_app ⦋n⦌) d) t
  change (SSet.stdSimplex.sdIso.inv.app ⦋n⦌).app d
    ((SSet.stdSimplex.sdIso.hom.app ⦋n⦌).app d t) = t at h
  change (SSet.sd.map (SSet.horn.ι k j hj)).app d
    ((SSet.stdSimplex.sdIso.inv.app ⦋n⦌).app d
      ((SSet.stdSimplex.sdIso.hom.app ⦋n⦌).app d t)) = s
  rw [h]
  exact ht

/--
概要：共通の標準単体から同じ余面の合成を与える二つの表示は、horn の細分でも一致する。
方針：horn の包含の単射性で元の二射を等置し、細分と標準同型の自然性で移す。
規約：中間の射は余面に限らず任意の単体圏の射でよい。
使われ方：二つの異なる余面から来る細分の元の一致。
-/
theorem hornSubdivisionFaceMap_common {n : ℕ} (k j l : Fin (n + 2))
    (hj : j ≠ k) (hl : l ≠ k) {m : SimplexCategory}
    (α β : m ⟶ ⦋n⦌) (hαβ : α ≫ SimplexCategory.δ j = β ≫ SimplexCategory.δ l) :
    SimplexCategory.sd.{u}.map α ≫ hornSubdivisionFaceMap n k j hj =
      SimplexCategory.sd.map β ≫ hornSubdivisionFaceMap n k l hl := by
  have hf : SSet.stdSimplex.map α ≫ SSet.horn.ι.{u} k j hj =
      SSet.stdSimplex.map β ≫ SSet.horn.ι k l hl := by
    apply (cancel_mono (SSet.horn (n + 1) k).ι).mp
    simp only [Category.assoc, SSet.horn.ι_ι]
    change SSet.stdSimplex.map α ≫ SSet.stdSimplex.map (SimplexCategory.δ j) =
      SSet.stdSimplex.map β ≫ SSet.stdSimplex.map (SimplexCategory.δ l)
    simpa only [SSet.stdSimplex.map_comp] using congrArg SSet.stdSimplex.map hαβ
  have hα : SimplexCategory.sd.map α ≫ SSet.stdSimplex.sdIso.inv.app ⦋n⦌ =
      SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map (SSet.stdSimplex.map α) :=
    SSet.stdSimplex.sdIso.inv.naturality α
  have hβ : SimplexCategory.sd.map β ≫ SSet.stdSimplex.sdIso.inv.app ⦋n⦌ =
      SSet.stdSimplex.sdIso.inv.app m ≫ SSet.sd.map (SSet.stdSimplex.map β) :=
    SSet.stdSimplex.sdIso.inv.naturality β
  change (SimplexCategory.sd.map α ≫ SSet.stdSimplex.sdIso.inv.app ⦋n⦌) ≫
      SSet.sd.map (SSet.horn.ι k j hj) =
    (SimplexCategory.sd.map β ≫ SSet.stdSimplex.sdIso.inv.app ⦋n⦌) ≫
      SSet.sd.map (SSet.horn.ι k l hl)
  rw [hα, hβ]
  simp only [Category.assoc, ← SSet.sd.map_comp, hf]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
