module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

/-!
概要：定値の単体的写像が、ホモトピー圏の任意の射を恒等射へ送ること。
方針：元の辺とその合成について帰納し、定値辺が退化辺であることを使う。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049）の関手性と、錐の固定した底の射。
規約：始域にも終域にも準圏性は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 定値写像は辺だけでなく、ホモトピー圏の任意の射を恒等射へ送る。 -/
lemma hoConstantMap_hom {A B : SSet.{u}} (b : B _⦋0⦌) {x y : hoFunctor.obj A}
    (β : x ⟶ y) :
    (hoFunctor.map (SSet.const b : A ⟶ B)).toFunctor.map β =
      𝟙 ((hoFunctor.map (SSet.const b : A ⟶ B)).toFunctor.obj x) := by
  induction β using SSet.HomotopyCategory.hom_rec with
  | homMk e =>
    change SSet.HomotopyCategory.homMk (e.map (SSet.const b)) = 𝟙 _
    have he : e.map (SSet.const b) = SSet.Edge.id ((SSet.const b : A ⟶ B).app (Opposite.op ⦋0⦌) _) := by
      apply SSet.Edge.ext
      change B.map ((⦋1⦌ : SimplexCategory).const ⦋0⦌ 0).op b =
        B.σ 0 (B.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op b)
      have h0 : (⦋0⦌ : SimplexCategory).const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
        exact Subsingleton.elim _ _
      have h1 : (⦋1⦌ : SimplexCategory).const ⦋0⦌ 0 = SimplexCategory.σ (0 : Fin 1) := by
        exact Subsingleton.elim _ _
      rw [h0, h1]
      simp only [CategoryTheory.op_id, Functor.map_id_apply]
      rfl
    rw [he, SSet.HomotopyCategory.homMk_id]
  | @comp x' y' z' f g hf hg =>
    rw [Functor.map_comp, hf, hg, Category.id_comp]
    obtain ⟨x0, rfl⟩ := (SSet.HomotopyCategory.objEquiv (X := A)).symm.surjective x'
    obtain ⟨y0, rfl⟩ := (SSet.HomotopyCategory.objEquiv (X := A)).symm.surjective y'
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
