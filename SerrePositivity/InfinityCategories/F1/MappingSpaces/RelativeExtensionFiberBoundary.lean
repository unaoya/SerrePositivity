module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecomposition
/-!
概要：固定境界内での相対延長の評価は元の境界射の関手頂点に定値となる。
方針：同じ相対制限を境界包含で分解し、固定 fiber の制限と頂点式を計算する。
規約：底・境界射・評価する元の射を保持し、充填性を仮定しない。
使われ方：全初点を固定する pointed 比較の初点像の恒等性。
-/

@[expose] public section
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- 概要：固定した境界を経由する評価射は同じ元の境界値に定値。
方針：相対制限の合成則と固定 fiber 包含の式を使う。
規約：全次数と元の境界射を保持。使われ方：指定比較の固定初点像。 -/
lemma relativeExtensionFiberEndpoint_eq_const_of_boundary {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (t : C ⟶ D) (b : B _⦋0⦌) (hj : (t ≫ i) ≫ a = SSet.const b)
    (g : C ⟶ vertexFiber p b) (hg : t ≫ v = g ≫ vertexFiberι p b) :
    relativeExtensionFiberEndpoint p a i v hv (t ≫ i) b hj = SSet.const (functorVertex g) := by
  unfold relativeExtensionFiberEndpoint
  rw [← relativeFunctorPre_comp]
  simp only [← Category.assoc]
  rw [relativeFunctorExtensionSpaceι_pre]
  simp only [SSet.const_comp]
  apply congrArg SSet.const
  have hpre := relativeFunctorPre_vertex p (i ≫ a) t v hv
  have ht := congrArg (fun z =>
    (eqToHom (congrArg (relativeFunctorSpace p) hj)).app (Opposite.op ⦋0⦌) z) hpre
  have htrans := ht.trans (relativeFunctorVertex_transport p hj (t ≫ v)
    (by simpa only [Category.assoc] using congrArg (fun k => t ≫ k) hv))
  have hvg : relativeFunctorVertex p (SSet.const b) (t ≫ v)
      (by rw [Category.assoc, hv, ← Category.assoc, hj]) =
      relativeFunctorVertex p (SSet.const b) (g ≫ vertexFiberι p b)
        (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]) := by
    apply Subtype.ext
    exact congrArg functorVertex hg
  exact (congrArg (fun z => (relativeFunctorConstFiberHom (A := C) p b).app
    (Opposite.op ⦋0⦌) z) htrans).trans
    ((congrArg (fun z => (relativeFunctorConstFiberHom (A := C) p b).app
      (Opposite.op ⦋0⦌) z) hvg).trans (relativeFunctorConstFiberHom_vertex p b g))
end SerrePositivity.InfinityCategories
