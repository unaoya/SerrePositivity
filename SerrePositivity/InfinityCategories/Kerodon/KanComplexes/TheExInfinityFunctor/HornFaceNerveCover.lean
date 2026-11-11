module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SimplexFaceRetraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.HornFacePoset

/-!
# horn の面の nerve の余面による被覆

概要：horn の面の nerve の任意の単体を、一つの余面の細分から持ち上げる。
方針：射列の最後の面に欠けた頂点を選び、その余面の分裂で全ての面を戻す。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の細分の像の同定への補助。
使われ方：実際の horn の細分から面の nerve への比較の全射性。

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
概要：安全な面の射列には、全ての面に共通して欠けた k 以外の頂点がある。
方針：最後の面に欠けた頂点は、それ以下の各面にも欠けている。
規約：射列は常に少なくとも一つの対象を持つ。
使われ方：余面の分裂で単体全体を戻す頂点の選択。
-/
theorem hornFaceNerve_missingVertex (n : ℕ) (k : Fin (n + 1))
    (d : SimplexCategoryᵒᵖ) (s : (nerve (HornFacePoset.{u} n k)).obj d) :
    ∃ j : Fin (n + 1), j ≠ k ∧ ∀ i, ULift.up j ∉ (s.obj i).val.finset := by
  obtain ⟨j, hj, hm⟩ := (s.obj (Fin.last d.unop.len)).property
  refine ⟨j, hj, fun i hi => hm ?_⟩
  have h : (s.obj i).val ≤ (s.obj (Fin.last d.unop.len)).val :=
    leOfHom (s.map (homOfLE (Fin.le_last i)))
  exact h hi

/--
概要：horn の面の nerve の任意の単体は、k と異なる一つの余面の細分の像に入る。
方針：全ての面に欠けた頂点を選び、余面の分裂で作った射列を余面で復元する。
規約：余面の次元は n から n+1。
使われ方：horn の細分比較の全射性の具体的な持ち上げ。
-/
theorem hornFaceNerve_faceCover (n : ℕ) (k : Fin (n + 2))
    (d : SimplexCategoryᵒᵖ) (s : (nerve (HornFacePoset.{u} (n + 1) k)).obj d) :
    ∃ j : Fin (n + 2), j ≠ k ∧ ∃ t : (SimplexCategory.sd.{u}.obj ⦋n⦌).obj d,
      (SimplexCategory.sd.map (SimplexCategory.δ j)).app d t =
        (nerveMap (hornFaceInclusion (n + 1) k).monotone.functor).app d s := by
  obtain ⟨j, hj, hm⟩ := hornFaceNerve_missingVertex (n + 1) k d s
  let R := NonemptyFiniteChains.orderHomMap
    (SimplexCategory.toPartOrd.map (simplexFaceRetraction j)).hom
  let t := s ⋙ (hornFaceInclusion (n + 1) k).monotone.functor ⋙ R.monotone.functor
  refine ⟨j, hj, t, ?_⟩
  apply nerve.ext_of_isThin
  funext i
  exact simplexFaceRetraction_chain j (s.obj i).val (hm i)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
