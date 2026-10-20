module
public import SerrePositivity.KST.SConstruction.DGExtensionParameterPullback
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameterValues

/-! # 実延長の値の tensor 作用とパラメータ射
概要：元の実延長の値への K tensor 作用が、K′→K と可換である。
方針：同じ値の currying と全 Hom 自然変換の引き戻しを照合する。
規約：実 coend の対象と射を保持する。使われ方：高次入力の単体的パラメータの作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の tensor chain map は、パラメータ複体の射を tensor した前合成と一致する。 -/
lemma dgModuleExtensionParameterValue_pullback {K L : Complex A} {F G : DGFunctor A D E}
    (a : L ⟶ K) (τ : DGFunctorParamTrans A D E K F G) (M : RightModule A D) (e : E) :
    dgModuleExtensionParameterValue A D E (dgParameterPullback A a τ) M e =
      (a ▷ ((dgModuleExtension A D E F).obj M).obj (op e)) ≫
        dgModuleExtensionParameterValue A D E τ M e := by
  apply (tensorRightHomEquiv (((dgModuleExtension A D E F).obj M).obj (op e)) L
    (((dgModuleExtension A D E G).obj M).obj (op e))).injective
  change curryRight (dgModuleExtensionParameterValue A D E (dgParameterPullback A a τ) M e) =
    curryRight ((a ▷ _) ≫ dgModuleExtensionParameterValue A D E τ M e)
  rw [dgModuleExtensionParameterValue_curry]
  have h := congrArg (fun σ => σ.app M ≫ moduleHomπ A E
      ((dgModuleExtension A D E F).obj M) ((dgModuleExtension A D E G).obj M) e)
    (dgModuleExtensionParameter_pullback A D E a τ)
  simp only [dgParameterPullback_app, Category.assoc] at h
  have hc := curryRight_naturality_source a (dgModuleExtensionParameterValue A D E τ M e)
  rw [dgModuleExtensionParameterValue_curry] at hc
  exact h.trans (by simpa only [tensorHom_id] using hc.symm)

end SerrePositivity.KST.SConstruction
