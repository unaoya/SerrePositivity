module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：薄い圏の nerve を標的とする射の内ホーンの持ち上げ。
方針：射列が頂点だけで決まり、二次元以上のホーンが全頂点を含むことを使う。
規約：始域には quasicategory 性、標的の圏には Hom の一意性を要求する。
使われ方：Kerodon §5.1.4（Tag 01U9）、Theorem 5.3.5.7（Tag 037Q）、有限鎖から区間への射の inner fibration 性。

対応節は Kerodon 4.1（Tag 01B8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-- 概要：薄い圏の nerve への二つの射は零次成分が同じなら等しい。
方針：各頂点を選ぶ単体圏の射について自然性を使い、射列の頂点を比較する。
規約：始域の単体集合に充填性を要求しない。
使われ方：Kerodon §1.3.3（Tag 002Y）、§5.1.4（Tag 01U9）、ホーンの制限の一意性。 -/
lemma thinNerve_hom_ext_vertices {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    {X : SSet.{u}} {f g : X ⟶ nerve C}
    (h : f.app (Opposite.op ⦋0⦌) = g.app (Opposite.op ⦋0⦌)) : f = g := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  let α : ⦋0⦌ ⟶ d.unop := SimplexCategory.const _ _ i
  have hf := congrArg (fun τ : (nerve C) _⦋0⦌ ↦ τ.obj 0)
    (ConcreteCategory.congr_hom (f.naturality α.op) s)
  have hg := congrArg (fun τ : (nerve C) _⦋0⦌ ↦ τ.obj 0)
    (ConcreteCategory.congr_hom (g.naturality α.op) s)
  change (f.app (Opposite.op ⦋0⦌) (X.map α.op s)).obj 0 = (f.app d s).obj i at hf
  change (g.app (Opposite.op ⦋0⦌) (X.map α.op s)).obj 0 = (g.app d s).obj i at hg
  rw [h] at hf
  exact hf.symm.trans hg

/-- 概要：薄い圏の nerve への単体の射は任意の二次元以上のホーンへの制限で決まる。
方針：全頂点がホーンに含まれることと頂点による外延性を使う。
規約：外側ホーンも含む。
使われ方：Kerodon §5.1.4（Tag 01U9）、有限鎖から区間への射の相対持ち上げ。 -/
lemma thinNerve_hom_ext_horn {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (n : ℕ) (i : Fin (n + 3)) {f g : (Δ[n + 2] : SSet.{u}) ⟶ nerve C}
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g := by
  apply thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro v
  exact congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) ⟨v, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn n i v⟩) h

/-- 概要：quasicategory から薄い圏の nerve への射は inner fibration。
方針：始域で内ホーンを充填し、標的のホーン制限の一意性で底との可換性を示す。
規約：薄い圏は半順序に限らない。
使われ方：Kerodon §5.1.4（Tag 01U9）、Theorem 5.3.5.7（Tag 037Q）、有限鎖の区間への射影。 -/
instance thinNerve_innerFibration {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    {X : SSet.{u}} [Quasicategory X] (p : X ⟶ nerve C) : InnerFibration p where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i h0 hn =>
      constructor
      intro a b sq
      obtain ⟨l, hl⟩ := Quasicategory.hornFilling h0 hn a
      refine CommSq.HasLift.mk' { l := l, fac_left := hl.symm, fac_right := ?_ }
      apply thinNerve_hom_ext_horn n i
      rw [← Category.assoc, ← hl]
      exact sq.w

/-- 概要：quasicategory から標準単体への任意の射は inner fibration。
方針：標準単体を有限順序の nerve に同型で移し、薄い圏の場合を使う。
規約：標準単体の次元は任意。
使われ方：Kerodon §5.1.4（Tag 01U9）、Theorem 5.3.5.7（Tag 037Q）、区間への射影の内ホーンの充填。 -/
instance stdSimplexTarget_innerFibration {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) (p : X ⟶ (Δ[n] : SSet.{u})) : InnerFibration p := by
  have hp : innerFibrations (p ≫ (stdSimplex.isoNerve n).hom) :=
    InnerFibration.mem (q := p ≫ (stdSimplex.isoNerve n).hom)
  rw [innerFibrations.cancel_right_of_respectsIso] at hp
  exact ⟨hp⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations
