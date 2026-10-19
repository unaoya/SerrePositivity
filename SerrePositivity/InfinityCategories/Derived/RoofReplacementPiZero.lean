module
public import SerrePositivity.InfinityCategories.Derived.RoofReplacementTransport
public import SerrePositivity.InfinityCategories.F1.SimplicialReplacementFunctor

/-! # 局所頂点持ち上げから replacement の連結成分上の全射性

概要：同じ添字からの細分後の係数の連結成分の持ち上げは、全空間の π₀ 上の全射性を与える。
方針：全頂点を係数頂点として表示し、指定細分の実輸送辺と係数の連結成分を接続する。
規約：添字の filteredness・係数の Kan 性は不要。使われ方：元の屋根比較の全空間の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite SSet
open scoped Simplicial
variable {C : Type u} [Category.{u} C]

/-- replacement の任意の零単体は、その始点の係数頂点の標準包含として表示できる。 -/
lemma roofReplacementVertex_eta (F : C ⥤ SSet.{u}) (z : (simplicialReplacement F) _⦋0⦌) :
    roofReplacementVertex F (z.1.obj 0) (SSet.yonedaEquiv z.2) = z := by
  obtain ⟨σ, τ⟩ := z
  refine Sigma.ext (ComposableArrows.ext₀ rfl) ?_
  apply heq_of_eq
  exact SSet.yonedaEquiv.symm_apply_apply τ

/-- 自然比較の全空間写像は、同じ添字の係数頂点で評価できる。 -/
lemma roofReplacementMap_vertex {F G : C ⥤ SSet.{u}} (η : F ⟶ G)
    (c : C) (g : (F.obj c) _⦋0⦌) :
    (simplicialReplacementMap η).app (op ⦋0⦌) (roofReplacementVertex F c g) =
      roofReplacementVertex G c ((η.app c).app (op ⦋0⦌) g) := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  exact SSet.yonedaEquiv_symm_comp g (η.app c)

/-- 局所的な細分後の連結成分の持ち上げから、全空間比較の π₀ の全射性を得る。 -/
theorem roofReplacementMap_piZero_surjective {F G : C ⥤ SSet.{u}} (η : F ⟶ G)
    (hl : ∀ (c : C) (g : (G.obj c) _⦋0⦌),
      ∃ (d : C) (r : c ⟶ d) (t : (F.obj d) _⦋0⦌),
        SSet.π₀.mk ((G.map r).app (op ⦋0⦌) g) =
          SSet.π₀.mk ((η.app d).app (op ⦋0⦌) t)) :
    Function.Surjective (SSet.mapπ₀ (simplicialReplacementMap η)) := by
  intro z
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective z
  rw [← roofReplacementVertex_eta G v]
  obtain ⟨d, r, t, ht⟩ := hl (v.1.obj 0) (SSet.yonedaEquiv v.2)
  refine ⟨SSet.π₀.mk (roofReplacementVertex F d t), ?_⟩
  rw [SSet.mapπ₀_mk, roofReplacementMap_vertex]
  have h := congrArg (SSet.mapπ₀ (simplicialReplacementConstantLift G d)) ht
  have he : SSet.π₀.mk (roofReplacementVertex G d ((G.map r).app (op ⦋0⦌)
      (SSet.yonedaEquiv v.2))) =
      SSet.π₀.mk (roofReplacementVertex G d ((η.app d).app (op ⦋0⦌) t)) := h
  exact he.symm.trans (roofReplacementTransport_piZero G r (SSet.yonedaEquiv v.2)).symm

end SerrePositivity.InfinityCategories
