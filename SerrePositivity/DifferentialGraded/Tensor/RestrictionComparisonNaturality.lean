module
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionComparison
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunction

/-! # 固定左因子とのtensorの制限比較自然変換

## 概要
固定左因子とのtensorの制限比較自然変換。

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
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 実際の閉零加群制限と固定左因子tensorに関する比較自然変換。 -/
def restrictionTensorComparison (N : LeftModule A E) :
    moduleRestriction A D E F.op ⋙ rightTensorFunctor A D (F.comp N) ⟶
      rightTensorFunctor A E N where
  app M := restrictionComparison A D E F (ForgetEnrichment.to (Complex A) M) N
  naturality {M M'} f := by
    apply hom_ext
    intro x
    have hD := ι_map A D ((moduleRestriction A D E F.op).map f)
      (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) x
    have hE := ι_map A E f (𝟙 (ForgetEnrichment.of (Complex A) N)) (F.obj x)
    simp only [moduleRestriction_map_eval, CategoryTheory.Functor.map_id] at hD hE
    change ι A D (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M))
      (F.comp N) x ≫ map A D ((moduleRestriction A D E F.op).map f)
        (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) ≫ _ = _
    calc
      _ = ((moduleEvaluation A E (F.obj x)).map f ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫
          ι A D (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M'))
            (F.comp N) x ≫ restrictionComparison A D E F
              (ForgetEnrichment.to (Complex A) M') N :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ restrictionComparison A D E F
            (ForgetEnrichment.to (Complex A) M') N) hD).trans (Category.assoc _ _ _))
      _ = ((moduleEvaluation A E (F.obj x)).map f ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫
          ι A E (ForgetEnrichment.to (Complex A) M') N (F.obj x) := by
        rw [ι_restrictionComparison]
      _ = ι A E (ForgetEnrichment.to (Complex A) M) N (F.obj x) ≫
          map A E f (𝟙 (ForgetEnrichment.of (Complex A) N)) := hE.symm
      _ = _ := (ι_restrictionComparison_assoc A D E F
        (ForgetEnrichment.to (Complex A) M) N x _).symm

lemma restrictionTensorComparison_app (N : LeftModule A E) (M : ModuleCategory A E) :
    (restrictionTensorComparison A D E F N).app M =
      restrictionComparison A D E F (ForgetEnrichment.to (Complex A) M) N := rfl

end SerrePositivity.DifferentialGraded.BalancedTensor
