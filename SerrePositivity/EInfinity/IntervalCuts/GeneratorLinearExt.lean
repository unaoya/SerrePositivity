module

public import SerrePositivity.EInfinity.IntervalCuts.VertexBasisEvaluation

/-!
# 語基底と区間生成元による三入力線形外延性

概要：Berger–Fresse §2.2.6 の語基底・二頂点・一辺の比較を三入力の線形写像へ延長する。
方針：整数次数比較、二重 curry、語基底と区間生成元の外延性を順に使う。
規約：任意の可換環と同じ宇宙の任意の標的加群。
使われ方：実際の余作用の部分合成則を全複体射へ束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory Surjection
open scoped TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：χ の負次数からの線形写像は移した語基底で決まる（BF §1.2.1）。
方針：整数次数比較同型の逆を前置し、語基底で比較する。
規約：標的は任意の A 加群。
使われ方：三入力比較の各係数を語基底へ帰着する。 -/
lemma complex_basis_linear_ext (n d : ℕ) {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (complex A n).X (-(d : ℤ)) →ₗ[A] M}
    (h : ∀ v : BasisWord n d,
      f ((complexXIso A n d).inv (basis A n d (ULift.up v))) =
        g ((complexXIso A n d).inv (basis A n d (ULift.up v)))) : f = g := by
  have H : f.comp (complexXIso A n d).inv.hom = g.comp (complexXIso A n d).inv.hom := by
    apply (basis A n d).ext
    intro v
    exact h v.down
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun l : degreeModule A n d →ₗ[A] M => l ((complexXIso A n d).hom x)) H
  simpa only [LinearMap.comp_apply, ModuleCat.inv_hom_apply] using! hx

/-- 概要：区間次数零からの線形写像は面表示の両頂点で決まる（BF §2.2.6）。
方針：既存の頂点加群射の外延性へ面生成元の同定を渡す。
規約：標的は任意の A 加群。
使われ方：三入力比較の最後の頂点入力。 -/
lemma vertexInput_linear_ext {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (interval A).X 0 →ₗ[A] M}
    (h : ∀ b, f (faceVector A (vertex b)) = g (faceVector A (vertex b))) : f = g := by
  have H : (ModuleCat.ofHom f : (interval A).X 0 ⟶ ModuleCat.of A M) = ModuleCat.ofHom g := by
    apply vertexInput_hom_ext A
    intro b
    exact (congrArg f (faceVector_vertex_eq A b).symm).trans
      ((h b).trans (congrArg g (faceVector_vertex_eq A b)))
  exact congrArg (fun l : (interval A).X 0 ⟶ ModuleCat.of A M => l.hom) H

/-- 概要：面表示の辺生成元は既存の正規化辺生成元（BF §2.2.1）。
方針：面鎖と辺鎖の一致を評価する。
規約：整数次数 −1 の元。
使われ方：辺生成元での線形外延性。 -/
lemma faceVector_edge_eq : (show (interval A).X (-1) from faceVector A edge) =
    (intervalXIso A 1).inv (edgeChain A) := by
  unfold faceVector
  rw [faceChain_edge]
  rfl

/-- 概要：区間次数 −1 からの線形写像は面表示の一辺で決まる（BF §2.2.6）。
方針：既存の辺加群射の外延性へ面生成元の同定を渡す。
規約：標的は任意の A 加群。
使われ方：三入力比較の最後の辺入力。 -/
lemma edgeInput_linear_ext {M : Type u} [AddCommGroup M] [Module A M]
    {f g : (interval A).X (-1) →ₗ[A] M}
    (h : f (faceVector A edge) = g (faceVector A edge)) : f = g := by
  have H : (ModuleCat.ofHom f : (interval A).X (-1) ⟶ ModuleCat.of A M) = ModuleCat.ofHom g := by
    apply edgeInput_hom_ext A
    exact (congrArg f (faceVector_edge_eq A).symm).trans
      (h.trans (congrArg g (faceVector_edge_eq A)))
  exact congrArg (fun l : (interval A).X (-1) ⟶ ModuleCat.of A M => l.hom) H

/-- 概要：二つの負次数係数と頂点成分からの線形写像は語基底と両頂点で決まる（BF §3.1）。
方針：テンソル線形写像を二回 curry し、二つの語基底と頂点外延性を適用する。
規約：内外 arity・次数は任意。
使われ方：部分合成則の頂点生成元から全係数への延長。 -/
lemma coefficient_vertex_linear_ext (m n d e : ℕ) {M : Type u} [AddCommGroup M] [Module A M]
    {f g : ((complex A m).X (-(d : ℤ)) ⊗[A] (complex A n).X (-(e : ℤ))) ⊗[A]
      (interval A).X 0 →ₗ[A] M}
    (h : ∀ (v : BasisWord m d) (w : BasisWord n e) (b : Fin 2),
      f (((complexXIso A m d).inv (basis A m d (ULift.up v)) ⊗ₜ[A]
        (complexXIso A n e).inv (basis A n e (ULift.up w))) ⊗ₜ[A] faceVector A (vertex b)) =
      g (((complexXIso A m d).inv (basis A m d (ULift.up v)) ⊗ₜ[A]
        (complexXIso A n e).inv (basis A n e (ULift.up w))) ⊗ₜ[A] faceVector A (vertex b))) :
    f = g := by
  apply TensorProduct.curry_injective
  apply TensorProduct.curry_injective
  apply complex_basis_linear_ext A m d
  intro v
  apply complex_basis_linear_ext A n e
  intro w
  apply vertexInput_linear_ext A
  intro b
  exact h v w b

/-- 概要：二つの負次数係数と辺成分からの線形写像は語基底と一辺で決まる（BF §3.1）。
方針：二回の curry に二つの語基底と辺外延性を適用する。
規約：内外 arity・次数は任意。
使われ方：部分合成則の辺生成元から全係数への延長。 -/
lemma coefficient_edge_linear_ext (m n d e : ℕ) {M : Type u} [AddCommGroup M] [Module A M]
    {f g : ((complex A m).X (-(d : ℤ)) ⊗[A] (complex A n).X (-(e : ℤ))) ⊗[A]
      (interval A).X (-1) →ₗ[A] M}
    (h : ∀ (v : BasisWord m d) (w : BasisWord n e),
      f (((complexXIso A m d).inv (basis A m d (ULift.up v)) ⊗ₜ[A]
        (complexXIso A n e).inv (basis A n e (ULift.up w))) ⊗ₜ[A] faceVector A edge) =
      g (((complexXIso A m d).inv (basis A m d (ULift.up v)) ⊗ₜ[A]
        (complexXIso A n e).inv (basis A n e (ULift.up w))) ⊗ₜ[A] faceVector A edge)) : f = g := by
  apply TensorProduct.curry_injective
  apply TensorProduct.curry_injective
  apply complex_basis_linear_ext A m d
  intro v
  apply complex_basis_linear_ext A n e
  intro w
  apply edgeInput_linear_ext A
  exact h v w

end SerrePositivity.EInfinity.IntervalCuts
