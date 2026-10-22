module

public import SerrePositivity.InfinityCategories.F2.FullyFaithfulVertexIsoImage

/-!
概要：元の二つの表現と指定比較から、同じ実両端を持つ比較を一意に反映する。
方針：指定比較を元の両端比較で挟み、同じ充満忠実な関手の逆像を取る。
規約：表現・模型側の指定比較を保持。使われ方：native 作用比較の正方形 hu。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A B : SSet.{u}} [Quasicategory A] [Quasicategory B] {f : A ⟶ B}
  (hf : IsFullyFaithful f) {x y : A _⦋0⦌} {z w : B _⦋0⦌}
  (ux : VertexIso (f.app _ x) z) (uy : VertexIso (f.app _ y) w) (m : VertexIso z w)

/-- 元の両表現と指定比較を保つ、同じ充満忠実な関手による比較の反映。 -/
def fullyFaithfulComparisonPreimage : VertexIso x y :=
  hf.preimageVertexIso (ux ≪≫ m ≪≫ uy.symm)

/-- 反映した同じ比較は、元の二表現と元の模型側比較の正方形を厳密に満たす。 -/
lemma fullyFaithfulComparisonPreimage_square :
    ux ≪≫ m = VertexIso.map (fullyFaithfulComparisonPreimage hf ux uy m) f ≪≫ uy := by
  rw [fullyFaithfulComparisonPreimage, vertexIso_map_preimage]
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- 同じ指定正方形を満たす比較は、元の充満忠実性による反映に厳密に一致する。 -/
lemma fullyFaithfulComparisonPreimage_unique (n : VertexIso x y)
    (hn : ux ≪≫ m = VertexIso.map n f ≪≫ uy) :
    n = fullyFaithfulComparisonPreimage hf ux uy m := by
  apply vertexIso_map_injective hf
  change VertexIso.map n f = VertexIso.map (hf.preimageVertexIso (ux ≪≫ m ≪≫ uy.symm)) f
  rw [vertexIso_map_preimage hf]
  have h := congrArg (fun e => e ≪≫ uy.symm) hn
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h.symm

end SerrePositivity.InfinityCategories.F2
