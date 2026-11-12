module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SimplexFaceRetraction

/-!
# 細分された余面の単射性と像からの持ち上げ

概要：標準単体の余面の細分の像を、欠けた頂点で判定する。
方針：余面の分裂を細分し、有限鎖の各対象で頂点の復元を使う。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分比較の単射性への補助。
使われ方：異なる余面から来る細分の元を共通の面から比較する。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory PartialOrder
open scoped _root_.Simplicial

/--
概要：像に頂点 j を含まない単体圏の射は、j 番目の余面に因子化する。
方針：余面の分裂で戻した後、各頂点での復元を使う。
規約：元の射の定義域の次元は任意。
使われ方：二つの余面の共通の小さい面の因子化。
-/
theorem simplexHom_factor_face {n : ℕ} {m : SimplexCategory} (j : Fin (n + 2))
    (θ : m ⟶ ⦋n + 1⦌) (hθ : ∀ i, θ i ≠ j) :
    (θ ≫ simplexFaceRetraction j) ≫ SimplexCategory.δ j = θ := by
  apply ConcreteCategory.hom_ext
  intro i
  exact simplexFaceRetraction_recover j (θ i) (hθ i)

/--
概要：細分された余面は各次数で単射である。
方針：余面の分裂を細分し、左逆との合成で像の等式を打ち消す。
規約：細分の一般の単射保存を仮定しない。
使われ方：一つの余面の表示の一意性。
-/
theorem subdivisionFace_app_injective {n : ℕ} (j : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((SimplexCategory.sd.{u}.map (SimplexCategory.δ j)).app d) := by
  intro a b h
  have h' := congrArg ((SimplexCategory.sd.map (simplexFaceRetraction j)).app d) h
  change ((SimplexCategory.sd.map (SimplexCategory.δ j) ≫
    SimplexCategory.sd.map (simplexFaceRetraction j)).app d) a =
    ((SimplexCategory.sd.map (SimplexCategory.δ j) ≫
      SimplexCategory.sd.map (simplexFaceRetraction j)).app d) b at h'
  rw [← SimplexCategory.sd.map_comp, simplexFaceRetraction_section,
    SimplexCategory.sd.map_id] at h'
  exact h'

/--
概要：細分された j 番目の余面の像の各面には頂点 j が含まれない。
方針：有限集合の像の元を取り出し、succAbove が欠けた頂点を取らないことを使う。
規約：細分の単体は非空な面の射列である。
使われ方：別の余面から来る像の共通の欠けた頂点。
-/
theorem subdivisionFace_avoids {n : ℕ} (j : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) (s : (SimplexCategory.sd.{u}.obj ⦋n⦌).obj d)
    (i : Fin (d.unop.len + 1)) :
    ULift.up j ∉ (((SimplexCategory.sd.map (SimplexCategory.δ j)).app d s).obj i).finset := by
  intro h
  obtain ⟨a, _, ha⟩ := (NonemptyFiniteChains.mem_map_iff (s.obj i)
    (SimplexCategory.toPartOrd.map (SimplexCategory.δ j)).hom (ULift.up j)).mp h
  have h' := congrArg ULift.down ha
  exact Fin.succAbove_ne j a.down h'

/--
概要：各面に頂点 j を含まない細分の単体は、細分された j 番目の余面から持ち上がる。
方針：余面の分裂を細分した写像で戻し、有限鎖の復元を各対象に適用する。
規約：細分の一般の引き戻し保存は用いない。
使われ方：共通の小さい面による二つの余面表示の比較。
-/
theorem subdivisionFace_lift {n : ℕ} (j : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) (s : (SimplexCategory.sd.{u}.obj ⦋n + 1⦌).obj d)
    (hs : ∀ i, ULift.up j ∉ (s.obj i).finset) :
    ∃ t : (SimplexCategory.sd.{u}.obj ⦋n⦌).obj d,
      (SimplexCategory.sd.map (SimplexCategory.δ j)).app d t = s := by
  refine ⟨(SimplexCategory.sd.map (simplexFaceRetraction j)).app d s, ?_⟩
  apply nerve.ext_of_isThin
  funext i
  exact simplexFaceRetraction_chain j (s.obj i) (hs i)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
