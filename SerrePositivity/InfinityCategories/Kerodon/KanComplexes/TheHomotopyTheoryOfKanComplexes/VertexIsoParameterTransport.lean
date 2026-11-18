module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：頂点のパラメータの等式による同じ同型の移送を、ホモトピー圏の射で計算する。
方針：等式の帰納法で恒等の移送へ戻す。
規約：HTT §1.2.4、Kerodon §4.4（Tag 01EM）の既存の頂点同型の計算法則。
使われ方：S8 の離散埋め込みの同じ頂点等式に沿う固定値比較の移送。
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 始点のパラメータの等式による同じ同型の型の移送は、等式の射の前合成。 -/
lemma vertexIso_parameter_source_cast_hom {X : SSet.{u}} {S : Sort v}
    (f : S → X _⦋0⦌) {a b : S} {c : X _⦋0⦌} (h : a = b) (e : VertexIso (f a) c) :
    (cast (congrArg (fun z => VertexIso (f z) c) h) e).hom =
      eqToHom (congrArg HomotopyCategory.mk (congrArg f h.symm)) ≫ e.hom := by
  cases h
  simp only [cast_eq, eqToHom_refl, Category.id_comp]

/-- 標的のパラメータの等式による同じ同型の型の移送は、等式の射の後合成。 -/
lemma vertexIso_parameter_target_cast_hom {X : SSet.{u}} {S : Sort v}
    (f : S → X _⦋0⦌) {a b : S} {c : X _⦋0⦌} (h : a = b) (e : VertexIso c (f a)) :
    (cast (congrArg (fun z => VertexIso c (f z)) h) e).hom =
      e.hom ≫ eqToHom (congrArg HomotopyCategory.mk (congrArg f h)) := by
  cases h
  simp only [cast_eq, eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
