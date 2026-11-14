module
public import SerrePositivity.HomologicalAlgebra.FreeWeightEndEvaluation

/-!
概要：自由単位重みendの逆評価は、同じ自由生成元を元の図式の射で評価する。
方針：恒等生成元での両逆則と元の自然変換の自然性を使う。
規約：IS-W2 C01の既存Yoneda・係数移送の評価則。
使われ方：HA 1.2.4、同じ第0頂点を通るTot標準脚の計算。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 同じ自由単位重みの逆評価は、元の図式の同じ射の作用を生成元に返す。 -/
theorem freeUnitWeightEndNatIso_inv_generator (j i : J) (f : i ⟶ j)
    (X : Jᵒᵖ ⥤ Complex A) (q : ℤ) (x : (X.obj (op j)).X q) :
    ((((freeUnitWeightEndNatIso A j).inv.app X).f q x).app (op i))
      (Sigma.ι (fun _ : i ⟶ j => ModuleCat.of A A) f (1 : A)) =
    (X.map f.op).f q x := by
  let e := (freeUnitWeightEndNatIso A j).app X
  let z := e.inv.f q x
  have hu := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f q) e.inv_hom_id) x
  change ((freeUnitWeightEndNatIso A j).hom.app X).f q z = x at hu
  rw [freeUnitWeightEndNatIso_hom_f_apply] at hu
  change (z.app (op j)) (Sigma.ι (fun _ : j ⟶ j => ModuleCat.of A A) (𝟙 j) (1 : A)) =
    x at hu
  have h := congrArg (fun k => Sigma.ι (fun _ : j ⟶ j => ModuleCat.of A A) (𝟙 j) ≫ k)
    (z.naturality f.op)
  have hv := ConcreteCategory.congr_hom h (1 : A)
  simp [freePresheafFunctor, copowerFunctor] at hv
  change (z.app (op i)) (Sigma.ι (fun _ : i ⟶ j => ModuleCat.of A A) f (1 : A)) =
      (X.map f.op).f q
        ((z.app (op j)) (Sigma.ι (fun _ : j ⟶ j => ModuleCat.of A A) (𝟙 j) (1 : A))) at hv
  erw [hu] at hv
  exact hv

end SerrePositivity.HomologicalAlgebra
