module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomEvaluation
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeProjection
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackNativePre
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeEvaluationLaws

/-!
概要：元の局所 Hom の再底変換と結合共役は、同じセル間の直接の制限に厳密に一致する。
方針：全相対族を展開し、引き戻しの両射影で評価を照合する。
規約：全ての局所 Hom を扱い、大域 Hom の制限像には限定しない。
使われ方：二次元 Segal 制限と零次元での局所比較の厳密な接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 再底変換後の元の Hom の共役は、同じ底上の射による直接の元の制限そのもの。 -/
lemma cocartesianBaseChangeNativeHomIso_restriction
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
      (cocartesianBaseChangeNativeHomIso l k p q).hom =
    quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
      (cocartesianBaseChangeOverMap l k)) := by
  let R := (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)
  let H := (cocartesianBaseChangeNativeHomIso l k p q).hom
  let P := quasicategoryCoreMap (cocartesianPullbackNativePre p.val.hom q.val.hom
    (cocartesianBaseChangeOverMap l k))
  let j := (quasicategoryCore (cocartesianRelativeFunctorSpace
    (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)
    (pullback.fst (nerveMap (l ⋙ k)) q.val.hom))).ι ≫
    cocartesianRelativeFunctorInclusion
      (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)
      (pullback.fst (nerveMap (l ⋙ k)) q.val.hom)
  have : Mono j := by
    dsimp only [j, cocartesianRelativeFunctorInclusion]
    infer_instance
  change R ≫ H = P
  apply (cancel_mono j).mp
  apply relativeFunctorUncurry_injective
  apply pullback.hom_ext
  · exact (relativeFunctorUncurry_projection ((R ≫ H) ≫ j)).trans
      (relativeFunctorUncurry_projection (P ≫ j)).symm
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, s⟩
    have hI := cocartesianBaseChangeNativeHomIso_apply l k p q (R.app n s) (𝟙 n) x
    have hQ := congrArg (fun f ↦ f.app n
      (((R.app n s).val.val.val.app n (𝟙 n))
        ((cocartesianBaseChangeNativeAssociativity p.val.hom l k).inv.app n x)))
      (cocartesianBaseChangeNativeAssociativity_hom_snd q.val.hom l k)
    have hR := cocartesianPullbackNativeRestriction_apply_snd
      (pullback.fst (nerveMap k) p.val.hom) (pullback.fst (nerveMap k) q.val.hom)
      (Over.mk (nerveMap l)) s.val
      ((cocartesianBaseChangeNativeAssociativity p.val.hom l k).inv.app n x)
    have hS := congrArg (fun f ↦ f.app n x)
      (cocartesianBaseChangeNativeAssociativity_inv_projection l k p.val.hom)
    have hP := congrArg (fun f ↦ f.app n (x, s.val))
      (cocartesianPullbackNativePre_uncurry_snd p.val.hom q.val.hom
        (cocartesianBaseChangeOverMap l k)
        (𝟙 (cocartesianRelativeFunctorSpace
          (pullback.fst (nerveMap k) p.val.hom)
          (pullback.fst (nerveMap k) q.val.hom))))
    exact (congrArg ((pullback.snd (nerveMap (l ⋙ k)) q.val.hom).app n) hI).trans
      (hQ.trans ((congrArg ((pullback.snd (nerveMap k) q.val.hom).app n) hR).trans
        ((congrArg (fun y ↦ (pullback.snd (nerveMap k) q.val.hom).app n
          (s.val.val.val.app n (𝟙 n) y)) hS).trans hP.symm)))

end SerrePositivity.InfinityCategories
