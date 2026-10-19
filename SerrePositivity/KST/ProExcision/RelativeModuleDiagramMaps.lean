module
public import SerrePositivity.KST.ProExcision.RelativeModuleDiagram

/-!
# 実相対商図式の可換正方形からの実写像

概要：二つの加群図式の実正方形を実相対商図式の自然変換へ降ろす。
方針：既存の実相対写像の合成則と右側の自然性で検証する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。使われ方：安定相対零化の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u r v w
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits
variable {R : Type r} [Ring R] {J : Type v} [Category.{w} J]
variable {A B A' B' : J ⥤ ModuleCat.{u} R}

/-- 概要：実相対商写像と通常の商射影の実可換性。
方針：商に入る前の実元で二つの合成を評価する。
規約：KST App. A。使われ方：実相対余極限同型の自然性。 -/
lemma relativeModuleMap_projection {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (h : f ≫ b = a ≫ f') :
    ModuleCat.ofHom f.hom.range.mkQ ≫ relativeModuleMap f f' a b h =
      b ≫ ModuleCat.ofHom f'.hom.range.mkQ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- 概要：実自然変換の可換正方形が実相対商図式に誘導する自然変換。
方針：各成分の実相対写像を取り、合成則で自然性を実右側正方形へ帰着する。
規約：SW92 Lemma 1.4。使われ方：相対商の実余極限への誘導写像。 -/
def relativeModuleDiagramMap {f : A ⟶ B} {f' : A' ⟶ B'}
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    relativeModuleDiagram f ⟶ relativeModuleDiagram f' where
  app j := relativeModuleMap _ _ (a.app j) (b.app j)
    (congrArg (fun t ↦ t.app j) h)
  naturality {i j} φ := by
    change relativeModuleMap (f.app i) (f.app j) (A.map φ) (B.map φ) (f.naturality φ).symm ≫
        relativeModuleMap (f.app j) (f'.app j) (a.app j) (b.app j)
          (congrArg (fun t ↦ t.app j) h) =
      relativeModuleMap (f.app i) (f'.app i) (a.app i) (b.app i)
          (congrArg (fun t ↦ t.app i) h) ≫
        relativeModuleMap (f'.app i) (f'.app j) (A'.map φ) (B'.map φ) (f'.naturality φ).symm
    rw [relativeModuleMap_comp, relativeModuleMap_comp]
    apply relativeModuleMap_eq_of_right_eq
    exact b.naturality φ

/-- 概要：実商図式の射影は実正方形から誘導した実写像に自然。
方針：各成分で実商射影の可換性を使う。
規約：KST Proposition 4.14。使われ方：実相対余極限比較の実正方形。 -/
lemma relativeModuleDiagramMap_projection {f : A ⟶ B} {f' : A' ⟶ B'}
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ f') :
    relativeModuleDiagramProjection f ≫ relativeModuleDiagramMap a b h =
      b ≫ relativeModuleDiagramProjection f' := by
  apply NatTrans.ext
  funext j
  exact relativeModuleMap_projection (f.app j) (f'.app j) (a.app j) (b.app j)
    (congrArg (fun t ↦ t.app j) h)

end SerrePositivity.KST.ProExcision
