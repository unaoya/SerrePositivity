module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Products.Basic

/-!
概要：離散な族の同じ圏の nerve を、元の nerve の余積として表示する。
方針：各単体の離散番号が全頂点で一定であることから、余積の普遍射を次数ごとに作る。
規約：全単体集合の strict な余積であり、標的の ∞ 余極限と区別する。
使われ方：P-11 の可算個の区間を小余積として扱うための形状表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (I C : Type u) [SmallCategory C]

/-- 概要：同じ圏の指定した離散成分を全族へ入れる。
方針：対象・射の両方に固定した離散番号を添える。
規約：元の成分の全射を保つ。
使われ方：離散な区間族の余積包含。 -/
def discreteProductNerveInclusion (i : I) : nerve C ⟶ nerve (Discrete I × C) :=
  nerveMap (CategoryTheory.Prod.sectR (Discrete.mk i) C)

/-- 概要：離散成分の番号は、一つの全単体の全頂点で一定。
方針：最初の頂点から指定頂点への射の離散成分を読む。
規約：対象の等式を返し、同型に弱めない。
使われ方：余積からの普遍射の自然性。 -/
lemma discreteProductNerve_index_eq {n : ℕ}
    (s : ComposableArrows (Discrete I × C) n) (i : Fin (n + 1)) :
    (s.obj i).1.as = (s.obj 0).1.as :=
  (Discrete.eq_of_hom (s.map (homOfLE (Fin.zero_le i))).1).symm

/-- 概要：各成分上の単体集合写像を、離散な全族上の一つの写像へ貼る。
方針：単体の最初の離散番号で成分写像を選び、残りの圏成分へ適用する。
規約：各成分の全高次単体を保持する。
使われ方：区間族の余積表示の普遍射。 -/
def discreteProductNerveDesc {X : SSet.{u}} (f : I → (nerve C ⟶ X)) :
    nerve (Discrete I × C) ⟶ X where
  app n := ↾fun s ↦ (f (s.obj 0).1.as).app n (s ⋙ CategoryTheory.Prod.snd _ _)
  naturality n m α := by
    rcases n with ⟨⟨n⟩⟩
    rcases m with ⟨⟨m⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    change (f (s.obj (α.unop.toOrderHom 0)).1.as).app _ _ =
        X.map α ((f (s.obj 0).1.as).app _ _)
    rw [discreteProductNerve_index_eq I C s]
    exact ConcreteCategory.congr_hom ((f (s.obj 0).1.as).naturality α)
      (s ⋙ CategoryTheory.Prod.snd _ _)

/-- 概要：貼った写像を一つの離散成分へ制限すると指定写像を回収する。
方針：最初の離散番号と圏射影を計算する。
規約：写像の厳密な等式。
使われ方：余積の普遍性の存在部分。 -/
lemma discreteProductNerveInclusion_desc {X : SSet.{u}} (f : I → (nerve C ⟶ X)) (i : I) :
    discreteProductNerveInclusion I C i ≫ discreteProductNerveDesc I C f = f i := by
  rfl

/-- 概要：全単体はその離散番号と元の圏成分から厳密に復元できる。
方針：離散番号の定値性と、成分ごとの射の等式を使う。
規約：頂点だけでなく全単体の等式。
使われ方：余積表示の普遍射の一意性。 -/
lemma discreteProductNerve_reconstruct {n : ℕ}
    (s : ComposableArrows (Discrete I × C) n) :
    (s ⋙ CategoryTheory.Prod.snd _ _) ⋙
      CategoryTheory.Prod.sectR (Discrete.mk (s.obj 0).1.as) C = s := by
  refine CategoryTheory.Functor.ext (F := (s ⋙ CategoryTheory.Prod.snd _ _) ⋙
    CategoryTheory.Prod.sectR (Discrete.mk (s.obj 0).1.as) C) (G := s) ?_ ?_
  · intro i
    exact Prod.ext (Discrete.ext (discreteProductNerve_index_eq I C s i).symm) rfl
  intro i j f
  apply CategoryTheory.Prod.hom_ext
  · exact Subsingleton.elim _ _
  · simp [CategoryTheory.Prod.sectR]

/-- 概要：離散な全族からの写像は、元の各成分への制限で決まる。
方針：各全単体を一つの成分から復元する。
規約：任意の単体集合を標的に許す。
使われ方：区間族の余積表示と写像の外延性。 -/
lemma discreteProductNerve_hom_ext {X : SSet.{u}} {f g : nerve (Discrete I × C) ⟶ X}
    (h : ∀ i, discreteProductNerveInclusion I C i ≫ f =
      discreteProductNerveInclusion I C i ≫ g) : f = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have he := congrArg (fun k ↦ k.app _ (s ⋙ CategoryTheory.Prod.snd _ _))
    (h (s.obj 0).1.as)
  change f.app _ ((s ⋙ CategoryTheory.Prod.snd _ _) ⋙
    CategoryTheory.Prod.sectR (Discrete.mk (s.obj 0).1.as) C) =
      g.app _ ((s ⋙ CategoryTheory.Prod.snd _ _) ⋙
        CategoryTheory.Prod.sectR (Discrete.mk (s.obj 0).1.as) C) at he
  simpa only [discreteProductNerve_reconstruct I C s] using he

/-- 概要：離散な族の nerve は、元の各成分の同じ strict 余積。
方針：構成した普遍射と、各成分への制限による外延性を組み合わせる。
規約：空の族も扱い、標的圏の ∞ 余極限を仮定しない。
使われ方：可算区間の族を余積として計算する。 -/
def discreteProductNerveCofan_isColimit :
    IsColimit (Cofan.mk (nerve (Discrete I × C)) (discreteProductNerveInclusion I C)) :=
  Cofan.IsColimit.mk _
    (fun c ↦ discreteProductNerveDesc I C (fun i ↦ c.ι.app ⟨i⟩))
    (fun c i ↦ discreteProductNerveInclusion_desc I C _ i)
    (fun c m hm ↦ discreteProductNerve_hom_ext I C (fun i ↦ by
      rw [discreteProductNerveInclusion_desc]
      exact hm i))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
