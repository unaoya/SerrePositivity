module
public import SerrePositivity.DifferentialGraded.Tensor.ResolvedRestrictionCoherence

/-! # 制限後の指定モデルによるtensor比較の恒等dg関手に関する整合性

## 概要
制限後の指定モデルによるtensor比較の恒等dg関手に関する整合性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
lemma restrictionLeft_id (N : LeftModule A D) : (DGFunctor.id D).comp N = N := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- 恒等制限による左作用の表示を元に戻すtensor同型。 -/
def resolvedRestrictionIdTensorIso (S : RightModule A D) (N : LeftModule A D) :
    obj A D S ((DGFunctor.id D).comp N) ≅ obj A D S N :=
  changeLeft A D S (restrictionLeft_id A D N)

@[reassoc]
lemma ι_resolvedRestrictionIdTensorIso_hom (S : RightModule A D) (N : LeftModule A D) (d : D) :
    ι A D S ((DGFunctor.id D).comp N) d ≫ (resolvedRestrictionIdTensorIso A D S N).hom =
      ι A D S N d :=
  (ι_changeLeft_hom A D S (restrictionLeft_id A D N) d).trans (Category.id_comp _)

/-- 恒等制限への指定増大を元の右加群への射として読む。 -/
def resolvedRestrictionAugmentationId {S M : ModuleCategory A D}
    (q : S ⟶ (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M) : S ⟶ M :=
  q ≫ (moduleRestrictionIdObjIso A D M).hom

@[simp]
lemma resolvedRestrictionAugmentationId_eval {S M : ModuleCategory A D}
    (q : S ⟶ (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M) (d : D) :
    (moduleEvaluation A D d).map (resolvedRestrictionAugmentationId A D q) =
      (moduleEvaluation A D d).map q := by
  rw [resolvedRestrictionAugmentationId, CategoryTheory.Functor.map_comp,
    moduleRestrictionIdObjIso_hom_eval, Category.comp_id]

/-- 恒等dg関手の比較は、表示を戻して指定増大とtensorする写像そのもの。 -/
lemma resolvedRestrictionComparison_id {S M : ModuleCategory A D}
    (q : S ⟶ (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M) (N : LeftModule A D) :
    resolvedRestrictionComparison A D D (DGFunctor.id D) q N =
      (resolvedRestrictionIdTensorIso A D (ForgetEnrichment.to (Complex A) S) N).hom ≫
        (rightTensorFunctor A D N).map (resolvedRestrictionAugmentationId A D q) := by
  apply hom_ext A D (ForgetEnrichment.to (Complex A) S) ((DGFunctor.id D).comp N)
  intro d
  rw [ι_resolvedRestrictionComparison, ι_resolvedRestrictionIdTensorIso_hom_assoc]
  have hmap := ι_map A D (resolvedRestrictionAugmentationId A D q)
    (𝟙 (ForgetEnrichment.of (Complex A) N)) d
  simp only [CategoryTheory.Functor.map_id, resolvedRestrictionAugmentationId_eval] at hmap
  exact hmap.symm

end SerrePositivity.DifferentialGraded.BalancedTensor
