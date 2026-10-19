module
public import SerrePositivity.KST.ProExcision.RelativeModule

/-!
# 実可換な同型正方形による相対加群の同型

概要：二つの実加群同型の可換正方形から像による商の実同型を作る。
方針：実逆射の可換性を証明し、既存の商写像の合成則を用いる。
規約：KST Appendix A、Proposition 4.14。使われ方：行側への実相対比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u r
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {R : Type r} [Ring R]

/-- 概要：恒等可換正方形の実相対写像は恒等射。
方針：通常商の代表元で定義を評価する。
規約：KST App. A。使われ方：実相対同型の逆射の検証。 -/
lemma relativeModuleMap_id {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (h : f ≫ 𝟙 N = 𝟙 M ≫ f) : relativeModuleMap f f (𝟙 M) (𝟙 N) h = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

/-- 概要：実同型の可換正方形は逆射でも可換。
方針：二つの実逆射を正方形の両辺に合成する。
規約：KST App. A。使われ方：像の商の逆写像の定義。 -/
lemma relativeSquare_inverse {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (a : M ≅ M') (b : N ≅ N')
    (h : f ≫ b.hom = a.hom ≫ f') : f' ≫ b.inv = a.inv ≫ f := by
  calc
    f' ≫ b.inv = (a.inv ≫ (a.hom ≫ f')) ≫ b.inv := by simp
    _ = (a.inv ≫ (f ≫ b.hom)) ≫ b.inv := by rw [h]
    _ = a.inv ≫ f := by simp

/-- 概要：実同型の可換正方形から得る相対加群の実同型。
方針：正方形と逆正方形の実商写像を合成し、恒等正方形に帰着する。
規約：KST Proposition 4.14、SW92 §1.2。新しいホモロジー仮定は不要。
使われ方：行側と列側の実相対 bar 同型。 -/
def relativeModuleIso {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (a : M ≅ M') (b : N ≅ N')
    (h : f ≫ b.hom = a.hom ≫ f') : relativeModule f ≅ relativeModule f' where
  hom := relativeModuleMap f f' a.hom b.hom h
  inv := relativeModuleMap f' f a.inv b.inv (relativeSquare_inverse f f' a b h)
  hom_inv_id := by
    rw [relativeModuleMap_comp]
    simp only [a.hom_inv_id, b.hom_inv_id, relativeModuleMap_id]
  inv_hom_id := by
    rw [relativeModuleMap_comp]
    simp only [a.inv_hom_id, b.inv_hom_id, relativeModuleMap_id]

end SerrePositivity.KST.ProExcision
