module
public import SerrePositivity.InfinityCategories.F1B.Localization.DeformationLocalization
/-!
概要：頂点全部分圏に両端を持つ実ホモトピーを、元の円柱写像から持ち上げる。
方針：円柱の各頂点の時刻を零または一に分け、両端の所属条件を使う。
規約：同じ全単体の写像を保持する。使われ方：K-flat 入力上の分解比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
/-- 円柱上の実ホモトピーの各頂点は、両端と同じ頂点全部分圏に属する。 -/
lemma fullSubcomplex_homotopy_vertex_mem {A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (f g : A ⟶ (fullSubcomplexOnVertices X P : SSet))
    (H : SSet.Homotopy (f ≫ (fullSubcomplexOnVertices X P).ι)
      (g ≫ (fullSubcomplexOnVertices X P).ι))
    (x : (A ⊗ Δ[1]) _⦋0⦌) : P (H.h.app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨a, t⟩ := x
  obtain ⟨t, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
  fin_cases t
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ (Opposite.op ⦋0⦌)) a
    change H.h.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm 0) =
      (f.app (Opposite.op ⦋0⦌) a).val at h
    exact h.symm ▸ fullSubcomplexOnVertices_vertex _
  · have h := ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ (Opposite.op ⦋0⦌)) a
    change H.h.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm 1) =
      (g.app (Opposite.op ⦋0⦌) a).val at h
    exact h.symm ▸ fullSubcomplexOnVertices_vertex _
/-- 両端を保持し、同じ実円柱写像を頂点全部分圏へ持ち上げる。 -/
def fullSubcomplexHomotopyLift {A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (f g : A ⟶ (fullSubcomplexOnVertices X P : SSet))
    (H : SSet.Homotopy (f ≫ (fullSubcomplexOnVertices X P).ι)
      (g ≫ (fullSubcomplexOnVertices X P).ι)) : SSet.Homotopy f g where
  h := fullSubcomplexLift P H.h (fullSubcomplex_homotopy_vertex_mem P f g H)
  h₀ := by
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).1
    rw [Category.assoc, fullSubcomplexLift_ι]
    exact H.h₀
  h₁ := by
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).1
    rw [Category.assoc, fullSubcomplexLift_ι]
    exact H.h₁
  rel := by
    ext n x
    exact False.elim x.1.2
/-- 持ち上げた全単体ホモトピーに包含を続けると、元の円柱写像を回収する。 -/
lemma fullSubcomplexHomotopyLift_ι {A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (f g : A ⟶ (fullSubcomplexOnVertices X P : SSet))
    (H : SSet.Homotopy (f ≫ (fullSubcomplexOnVertices X P).ι)
      (g ≫ (fullSubcomplexOnVertices X P).ι)) :
    (fullSubcomplexHomotopyLift P f g H).h ≫ (fullSubcomplexOnVertices X P).ι = H.h :=
  fullSubcomplexLift_ι P H.h (fullSubcomplex_homotopy_vertex_mem P f g H)
/-- 持ち上げた比較の同じ頂点辺を、元の同じ実辺として回収する。 -/
lemma fullSubcomplexHomotopyLift_vertex_val {A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (f g : A ⟶ (fullSubcomplexOnVertices X P : SSet))
    (H : SSet.Homotopy (f ≫ (fullSubcomplexOnVertices X P).ι)
      (g ≫ (fullSubcomplexOnVertices X P).ι)) (a : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (fullSubcomplexHomotopyLift P f g H) a).edge.val =
      (simplicialHomotopyVertexEdge H a).edge := rfl
end SerrePositivity.InfinityCategories
