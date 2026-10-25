module
public import SerrePositivity.DifferentialGraded.Module.ExtensionFreeUnitComparison
/-!
概要：任意の二つの自由加群間の閉射について、実延長と元の Hom 係数への作用を比較する。
方針：延長制限随伴と自由評価同値で射を検出し、自由制限比較の成分を用いる。
規約：同じ実延長関手・実端点同型を保ち、生成複体の次数を制限しない。
使われ方：c′ の全シフト自由閉射を端点輸送込みで共通提示へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

def dgFreeClosedArrowImage (x y : D) (K L : Complex R)
    (g : (freeAt x).obj K ⟶ (freeAt y).obj L) :
    (freeAt (F.obj x)).obj K ⟶ (freeAt (F.obj y)).obj L :=
  (freeHomEquiv R E (F.obj x) K ((freeAt (F.obj y)).obj L)).symm
    (freeHomEquiv R D x K ((freeAt y).obj L) g ≫ (𝟙 L ⊗ₘ F.map x y))

set_option maxRecDepth 1024 in
lemma dgModuleExtensionFreeAtIso_arrow_comm (x y : D) (K L : Complex R)
    (g : (freeAt x).obj K ⟶ (freeAt y).obj L) :
    (dgModuleExtension R D E F).onClosed.map g ≫ (dgModuleExtensionFreeAtIso R D E F y L).hom =
    (dgModuleExtensionFreeAtIso R D E F x K).hom ≫ dgFreeClosedArrowImage R D E F x y K L g := by
  apply ((dgModuleExtensionRestrictionAdjunction R D E F).homEquiv ((freeAt x).obj K)
    ((freeAt (F.obj y)).obj L)).injective
  apply (freeHomEquiv R D x K
    ((moduleRestriction R D E F.op).obj ((freeAt (F.obj y)).obj L))).injective
  rw [Adjunction.homEquiv_naturality_left, dgModuleExtensionFreeAtIso_adjunct,
    freeHomEquiv_naturality_right, freeRestrictionComparison_eval]
  rw [← dgModuleExtensionFreeAdjunction_homEquiv, dgModuleExtensionFreeAtIso_homEquiv]
  simp only [freeEvaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv,
    dgFreeClosedArrowImage, Equiv.apply_symm_apply]

end SerrePositivity.DifferentialGraded
