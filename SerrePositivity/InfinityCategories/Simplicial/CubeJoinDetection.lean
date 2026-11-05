module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.CubeVertexSupport
public import SerrePositivity.InfinityCategories.Simplicial.CubeMapGenerated

/-! # 具体的な立方体の join 射の有限データによる回収
概要：join を保つ頂点関数は、零頂点と一座標頂点での値から全て回収できる。
方針：底の像を残した有限 join の式を帰納し、元の頂点の support 表示へ適用する。
規約：一端点の定数射と零次元を含み、底の保存は仮定しない。
使われ方：具体的な cubical 射の正規形と語の表示非依存性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction

/-- join 射の有限 join での値は、零頂点の像と各一座標頂点の像の join。 -/
lemma cubeJoinMap_sup_atoms {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (s : Finset (Fin n)) :
    f (s.sup (cubeVertexAtom n)) = f ⊥ ⊔ s.sup (fun i => f (cubeVertexAtom n i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert, hf, ih, Finset.sup_insert]
    ac_rfl

/-- 元の全頂点での join 射の値は、その有限 support と指定した有限データから回収される。 -/
lemma cubeJoinMap_eval {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (x : CubeVertex n) :
    f x = f ⊥ ⊔ (cubeVertexSupport x).sup (fun i => f (cubeVertexAtom n i)) := by
  rw [← cubeJoinMap_sup_atoms hf]
  exact congrArg f (cubeVertexSupport_sup_atoms x).symm

/-- join 射は、元の零頂点と全ての一座標頂点での値だけで判定できる。 -/
lemma cubeJoinMap_ext {n m : ℕ} {f g : CubeVertex n → CubeVertex m}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (hg : ∀ x y, g (x ⊔ y) = g x ⊔ g y)
    (hzero : f ⊥ = g ⊥) (hatom : ∀ i, f (cubeVertexAtom n i) = g (cubeVertexAtom n i)) :
    f = g := by
  funext x
  rw [cubeJoinMap_eval hf x, cubeJoinMap_eval hg x, hzero]
  simp only [hatom]

/-- 具体的な生成関数は、元の零頂点と全ての一座標頂点での値で判定される。 -/
lemma cubeMapGenerated_ext {n m : ℕ} {f g : CubeVertex n → CubeVertex m}
    (hf : CubeMapGenerated f) (hg : CubeMapGenerated g)
    (hzero : f ⊥ = g ⊥) (hatom : ∀ i, f (cubeVertexAtom n i) = g (cubeVertexAtom n i)) :
    f = g :=
  cubeJoinMap_ext (cubeMapGenerated_sup hf) (cubeMapGenerated_sup hg) hzero hatom

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinMap_eval := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinMap_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinMap_ext := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinMap_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinMap_sup_atoms := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinMap_sup_atoms

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeMapGenerated_ext := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeMapGenerated_ext
