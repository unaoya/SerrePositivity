module

public import SerrePositivity.KST.DerivedGeometry.SequentialModuleDifference
public import SerrePositivity.KST.DerivedGeometry.SequentialHomotopyLimit

/-!
概要：加群逆系の圏論的な積の差分射の全射性。
方針：具体的な積加群との比較で差分方程式の構成済みの解を移す。
規約：係数環の可換性を仮定しない。
使われ方：TT §3、Toën §3.2、Stacks 15.88.12・36.3.4 の Milnor 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {H : Type u} [Ring H] (X : ℕ → ModuleCat.{u} H)
  (s : ∀ n, X (n + 1) ⟶ X n)

/--
概要：圏論的な積の差分と具体的な差分線形写像は同じ。
方針：具体的な積の各射影との合成で比較する。
規約：実際の差分射の等式を与える。
使われ方：TT §3、Stacks 36.3.4 の差分射の全射性。
-/
lemma moduleSequenceDifference_comparison :
    sequentialDifference X s ≫ (ModuleCat.piIsoPi X).hom =
      (ModuleCat.piIsoPi X).hom ≫ ModuleCat.ofHom (moduleSequenceDifference X s) := by
  apply (ModuleCat.productConeIsLimit X).hom_ext
  intro ⟨n⟩
  change sequentialDifference X s ≫ (ModuleCat.piIsoPi X).hom ≫
      ModuleCat.ofHom (LinearMap.proj n) = _
  rw [ModuleCat.piIsoPi_hom_ker_subtype, sequentialDifference_π]
  apply ModuleCat.hom_ext
  ext x
  have h₀ := congrArg (fun f => f x) (ModuleCat.piIsoPi_hom_ker_subtype X n)
  have h₁ := congrArg (fun f => f x) (ModuleCat.piIsoPi_hom_ker_subtype X (n + 1))
  change ((ModuleCat.piIsoPi X).hom x) n = (Pi.π X n) x at h₀
  change ((ModuleCat.piIsoPi X).hom x) (n + 1) = (Pi.π X (n + 1)) x at h₁
  change (Pi.π X n) x - s n ((Pi.π X (n + 1)) x) =
    ((ModuleCat.piIsoPi X).hom x) n - s n (((ModuleCat.piIsoPi X).hom x) (n + 1))
  rw [h₀, h₁]

/--
概要：全射な遷移射を持つ加群逆系の圏論的な差分射は全射。
方針：具体的な差分線形写像の全射性を比較同型で移す。
規約：任意の単位的係数環を許す。
使われ方：TT §3・§8、Stacks 15.88.12・36.3.4 の lim¹ 消滅。
-/
lemma sequentialDifference_epi_of_surjective
    (hs : ∀ n, Function.Surjective (s n)) : Epi (sequentialDifference X s) := by
  haveI : Epi (ModuleCat.ofHom (moduleSequenceDifference X s)) :=
    (ModuleCat.epi_iff_surjective _).mpr (moduleSequenceDifference_surjective X s hs)
  haveI : Epi (sequentialDifference X s ≫ (ModuleCat.piIsoPi X).hom) := by
    rw [moduleSequenceDifference_comparison]
    infer_instance
  exact (epi_comp_iff_of_isIso (sequentialDifference X s) (ModuleCat.piIsoPi X).hom).mp
    inferInstance

end SerrePositivity.KST.DerivedGeometry
