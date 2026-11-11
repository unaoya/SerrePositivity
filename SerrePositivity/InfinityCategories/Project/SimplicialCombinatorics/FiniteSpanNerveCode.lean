module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：三点の有限 span の nerve を標準の二次元 span ホーンへ写す。
方針：各鎖を頂点番号で符号化し、一つの鎖が両終点を含まないことを使う。
規約：元の全単体と頂点番号を保持する。
使われ方：Ind の小さい有限半順序形状と標準 span の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 標準二次元単体への全次数の符号化。 -/
def finiteSpanNerveCode : nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} ⟶ Δ[2] where
  app n := ↾fun s => stdSimplex.objEquiv.symm (SimplexCategory.mkHom
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode.comp (⟨s.obj, s.monotone⟩ : Fin (n.unop.len + 1) →o _)))
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply stdSimplex.ext
    intro i
    rfl

/-- 一つの鎖は二つの比較不能な終点を同時には含まない。 -/
lemma finiteSpanNerveCode_mem {n : SimplexCategoryᵒᵖ}
    (s : (nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u}).obj n) :
    finiteSpanNerveCode.app n s ∈ (horn 2 0).obj n := by
  have hv (v : Fin (n.unop.len + 1)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode (s.obj v) = 0 ∨
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode (s.obj v) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode (s.obj (Fin.last n.unop.len)) := by
    have h := s.monotone (Fin.le_last v)
    change (s.obj v).down = .zero ∨ (s.obj v).down = (s.obj (Fin.last n.unop.len)).down at h
    rcases h with h | h
    · exact Or.inl (by change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanVertexCode _ = 0; rw [h]; rfl)
    · exact Or.inr (congrArg _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanVertexCode h)
  apply (mem_horn_iff_notMem_range _ (0 : Fin 3)).mpr
  by_cases h : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode (s.obj (Fin.last n.unop.len)) = 1
  · refine ⟨2, by decide, ?_⟩
    rintro ⟨v, he⟩
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode (s.obj v) = 2 at he
    have hval := hv v
    rw [h] at hval
    omega
  · refine ⟨1, by decide, ?_⟩
    rintro ⟨v, he⟩
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanCode (s.obj v) = 1 at he
    have hval := hv v
    omega

/-- 同じ符号化を標準 span ホーンに制限する。 -/
def finiteSpanNerveToHorn : nerve _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FiniteSpanIndex.{u} ⟶ (horn 2 0 : SSet.{u}) :=
  Subcomplex.lift finiteSpanNerveCode (by
    intro n t ht
    obtain ⟨s, rfl⟩ := ht
    exact finiteSpanNerveCode_mem s)

/-- 元の標準単体への射を厳密に回収する。 -/
lemma finiteSpanNerveToHorn_ι : finiteSpanNerveToHorn.{u} ≫ (horn 2 0).ι =
    finiteSpanNerveCode := rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
