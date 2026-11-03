module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointComposition

/-!
概要：元の同じ全延長証拠の指定終点比較は、同じ実終点の恒等同型となる。
方針：元の三証拠の比較の合成則から可逆性で消去する。
規約：指定同型の値の等式。使われ方：普遍 prism の実制限での比較の簡約。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の同じ実延長・実終点の指定比較は、元の同じ頂点の恒等同型。 -/
lemma RelativeExtensionEndpointWitness.iso_refl
    {A D C E F B : SSet.{u}} {p : E ⟶ B} [LeftFibration p] {b : A ⟶ B}
    {i : D ⟶ A} {v : D ⟶ E} {j : C ⟶ A} {q : F ⟶ B} {a : C ⟶ F}
    (w : RelativeExtensionEndpointWitness p b i v j q a)
    (hi : leftAnodyneExtensions i) (hv : v ≫ p = i ≫ b) (hj : j ≫ b = a ≫ q) :
    w.iso w hi hv hj = Iso.refl _ := by
  let e := w.iso w hi hv hj
  have h := congrArg Iso.hom (w.iso_trans w w hi hv hj)
  change e.hom ≫ e.hom = e.hom at h
  have hc := congrArg (fun f => e.inv ≫ f) h
  apply Iso.ext
  change e.hom = 𝟙 _
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using hc

end SerrePositivity.InfinityCategories.F2
