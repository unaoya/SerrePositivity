module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialCofinalSubsequences
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation

/-!
概要：可算鎖の nerve を有限な始区間の増大列で覆う。
方針：単体の全頂点に上界を課し、有限個の頂点の最大値を取る。
規約：各段階は元の nerve の部分複体で、遷移写像を厳密に保持する。
使われ方：引き戻しの交互構成で有限段階の整合する全図式を貼り合わせる。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：可算鎖の最初の n+1 頂点が張る部分複体。
方針：単体を表す全鎖の各頂点に同じ上界を課す。
規約：高次単体を切り捨てず全部分 nerve を取る。
使われ方：可算全図式の有限な始区間。 -/
def sequentialNerveStage (n : ℕ) : (nerve (ULift.{u} ℕ)).Subcomplex where
  obj _ := {s | ∀ i, (s.obj i).down ≤ n}
  map {_ _} α _ hs i := hs ((SimplexCategory.toCat.map α.unop).toFunctor.obj i)

/-- 概要：可算鎖の始区間は増大列をなす。
方針：頂点の上界の推移性を使う。
規約：同じ単体の包含。
使われ方：図式の厳密な段階制限。 -/
lemma sequentialNerveStage_monotone : Monotone (sequentialNerveStage.{u}) := by
  intro n m h d s hs i
  exact (hs i).trans h

/-- 概要：有限な始区間の和は元の可算鎖の nerve 全体。
方針：指定された一つの単体の有限な頂点族の最大値を選ぶ。
規約：全次数での等式。
使われ方：段階から貼り合わせた図式の定義域を回収する。 -/
lemma iSup_sequentialNerveStage : (⨆ n, sequentialNerveStage.{u} n) = ⊤ := by
  apply le_antisymm le_top
  intro d s _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  refine ⟨Finset.univ.sup (fun i ↦ (s.obj i).down), ?_⟩
  intro i
  exact Finset.le_sup (f := fun j : Fin (d.unop.len + 1) ↦ (s.obj j).down)
    (Finset.mem_univ i)

/-- 概要：各有限始区間で厳密に整合する全図式は元の可算 nerve 上に貼り合う。
方針：部分複体の増大列の余極限の普遍性を使う。
規約：頂点・辺だけの整合で代用せず、各段階の全自然変換の等式を要求する。
使われ方：交互に延長した有限図式から一つの coherent な可算図式を得る。 -/
lemma exists_sequentialNerve_map {X : SSet.{u}}
    (f : ∀ n, (sequentialNerveStage.{u} n : SSet.{u}) ⟶ X)
    (hf : ∀ n m (h : n ≤ m),
      Subcomplex.homOfLE (sequentialNerveStage_monotone h) ≫ f m = f n) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n, (sequentialNerveStage n).ι ≫ F = f n := by
  let D := sequentialNerveStage_monotone.{u}.functor
  have htop : IsLUB (Set.range D.obj) ⊤ := by
    simpa only [D, Monotone.functor_obj, iSup_sequentialNerveStage] using
      (isLUB_iSup (f := sequentialNerveStage.{u}))
  let c := Preorder.colimitCoconeOfIsLUB D htop
  have hc := isColimitOfPreserves Subcomplex.toSSetFunctor c.isColimit
  let d : Cocone (D ⋙ Subcomplex.toSSetFunctor) :=
    { pt := X
      ι := { app := f
             naturality := fun n m h ↦ by
               change Subcomplex.homOfLE (sequentialNerveStage_monotone (leOfHom h)) ≫
                 f m = f n ≫ 𝟙 X
               rw [Category.comp_id]
               exact hf n m (leOfHom h) } }
  refine ⟨(Subcomplex.topIso _).inv ≫ hc.desc d, ?_⟩
  intro n
  have he : (sequentialNerveStage n).ι ≫ (Subcomplex.topIso _).inv =
      (Subcomplex.toSSetFunctor.mapCocone c.cocone).ι.app n := rfl
  rw [← Category.assoc, he, hc.fac]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
