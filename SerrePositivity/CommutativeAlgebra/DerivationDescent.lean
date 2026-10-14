module

public import SerrePositivity.CommutativeAlgebra.ModuleDerivationDescent

/-! # 全射な代数写像に沿う導分の降下

導分が写像の核を消すことを確認してから降下する。
対象は終域自身とし、始域からの作用は代数写像による標準作用を使う。
-/

@[expose] public section
namespace SerrePositivity

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- 核を消す導分を全射な代数写像の終域へ降ろす。 -/
noncomputable def descendDerivation
    (hf : Function.Surjective (algebraMap S T)) (δ : Derivation R S T)
    (hδ : ∀ x, algebraMap S T x = 0 → δ x = 0) : Derivation R T T :=
  descendModuleDerivation hf δ hδ

/-- 降下は元の導分と実際に両立する。 -/
theorem descendDerivation_apply
    (hf : Function.Surjective (algebraMap S T)) (δ : Derivation R S T)
    (hδ : ∀ x, algebraMap S T x = 0 → δ x = 0) (x : S) :
    descendDerivation hf δ hδ (algebraMap S T x) = δ x :=
  descendModuleDerivation_apply hf δ hδ x

end SerrePositivity
