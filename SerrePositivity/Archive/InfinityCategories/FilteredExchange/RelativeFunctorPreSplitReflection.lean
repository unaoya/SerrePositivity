module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorOverPrecomposition

/-!
概要：切断を持つ全係数の追加は、元の指定相対頂点同型の等式を反映する。
方針：元の切断で戻し、ホモトピー圏の関手性と恒等射の像を使う。
規約：元の端点と指定値を保持。使われ方：全選択族の三関係を元の全空間の比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定頂点同型は、厳密な戻り射を持つ像の指定値から一意に回収できる。 -/
lemma vertexIso_map_injective_of_retraction {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : f ≫ g = 𝟙 X) {x y : X _⦋0⦌} :
    Function.Injective (fun e : VertexIso x y => VertexIso.map e f) := by
  intro e e' he
  have hm := congrArg (fun k => VertexIso.map k g) he
  rw [vertexIso_map_comp, vertexIso_map_comp] at hm
  have hi (a : VertexIso x y) : VertexIso.map a (𝟙 X) = a := by
    have hh : (hoFunctor.map (𝟙 X)).toFunctor = 𝟭 (hoFunctor.obj X) := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    exact eq_of_heq (mapIso_heq_of_functor_eq hh a)
  have h₀ := (vertexIso_map_heq e h).trans (heq_of_eq (hi e))
  have h₁ := (vertexIso_map_heq e' h).trans (heq_of_eq (hi e'))
  exact eq_of_heq (h₀.symm.trans ((heq_of_eq hm).trans h₁))

/-- 底上の元の射に切断があれば、その相対前合成は元の指定比較の等式を反映する。 -/
lemma relativeFunctorOverPre_vertexIso_injective_of_section {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) (s : b ⟶ a) (hs : s ≫ f = 𝟙 b)
    {x y : (relativeFunctorSpace p b.hom) _⦋0⦌} :
    Function.Injective (fun e : VertexIso x y => VertexIso.map e (relativeFunctorOverPre p f)) :=
  vertexIso_map_injective_of_retraction (relativeFunctorOverPre p f) (relativeFunctorOverPre p s)
    (by rw [← relativeFunctorOverPre_comp, hs, relativeFunctorOverPre_id])

/-- 点を持つ全係数を追加した相対前合成は、元の指定比較の等式を反映する。 -/
lemma relativeFunctorTensorPre_vertexIso_injective {C E K B : SSet.{u}}
    (p : E ⟶ B) (a : C ⟶ B) (v : K _⦋0⦌)
    {x y : (relativeFunctorSpace p a) _⦋0⦌} :
    Function.Injective (fun e : VertexIso x y =>
      VertexIso.map e (relativeFunctorPre p a (fst C K))) := by
  let f : Over.mk (fst C K ≫ a) ⟶ Over.mk a := Over.homMk (fst C K) rfl
  let s : Over.mk a ⟶ Over.mk (fst C K ≫ a) :=
    Over.homMk (U := Over.mk a) (V := Over.mk (fst C K ≫ a))
      (lift (𝟙 C) (SSet.const v)) (by
        change lift (𝟙 C) (SSet.const v) ≫ (fst C K ≫ a) = a
        rw [← Category.assoc, lift_fst, Category.id_comp])
  have hs : s ≫ f = 𝟙 (Over.mk a) := by
    apply Over.OverMorphism.ext
    exact lift_fst _ _
  exact relativeFunctorOverPre_vertexIso_injective_of_section p f s hs

end SerrePositivity.InfinityCategories.F2
