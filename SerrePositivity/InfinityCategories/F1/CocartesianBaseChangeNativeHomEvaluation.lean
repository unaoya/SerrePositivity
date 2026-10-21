module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeNativeObjectIso
public import SerrePositivity.InfinityCategories.F1.CocartesianNativeHomWhisker

/-!
概要：元の全相対 Hom の結合共役を、元の全空間の前後合成として評価する。
方針：豊穣 Hom の共役を展開し、任意の次数とパラメーター制限で計算する。
規約：全ての局所 Hom を扱い、大域 Hom からの制限の像には限定しない。
使われ方：元の Segal 制限の共有頂点での厳密な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全相対 Hom の同じ共役は、全パラメーターで全空間の実際の前後合成。 -/
lemma cocartesianBaseChangeNativeHomIso_apply
    {n m : SimplexCategoryᵒᵖ}
    (s : (SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))).obj n)
    (α : n ⟶ m) (x : (pullback (nerveMap (l ⋙ k)) p.val.hom).obj m) :
    (((cocartesianBaseChangeNativeHomIso l k p q).hom.app n s).val.val.val.app m α) x =
      (cocartesianBaseChangeNativeAssociativity q.val.hom l k).hom.app m
        (s.val.val.val.app m α
          ((cocartesianBaseChangeNativeAssociativity p.val.hom l k).inv.app m x)) := by
  change (((eHomWhiskerLeft SSet.{u}
    ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
    (cocartesianBaseChangeNativeObjectIso l k q).hom).app n
      ((eHomWhiskerRight SSet.{u} (cocartesianBaseChangeNativeObjectIso l k p).inv
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj
            q))).app n s)).val.val.val.app m α) x = _
  rw [cocartesianNativeHomWhiskerLeft_apply, cocartesianNativeHomWhiskerRight_apply]
  rfl

/-- 同じ共役の族を展開すると、全空間の結合同型による実際の前後合成になる。 -/
lemma cocartesianBaseChangeNativeHomIso_uncurry {T : SSet.{u}}
    (t : T ⟶ SimplicialCategory.sHom
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) :
    relativeFunctorUncurry (t ≫ (cocartesianBaseChangeNativeHomIso l k p q).hom ≫
      (quasicategoryCore (cocartesianRelativeFunctorSpace
        (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)
        (pullback.fst (nerveMap (l ⋙ k)) q.val.hom))).ι ≫
      cocartesianRelativeFunctorInclusion
        (pullback.fst (nerveMap (l ⋙ k)) p.val.hom)
        (pullback.fst (nerveMap (l ⋙ k)) q.val.hom)) =
    ((cocartesianBaseChangeNativeAssociativity p.val.hom l k).inv ▷ T) ≫
      relativeFunctorUncurry (t ≫ (quasicategoryCore (cocartesianRelativeFunctorSpace
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom))
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) q.val.hom)))).ι ≫
        cocartesianRelativeFunctorInclusion
          (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p.val.hom))
          (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) q.val.hom))) ≫
      (cocartesianBaseChangeNativeAssociativity q.val.hom l k).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, z⟩
  exact cocartesianBaseChangeNativeHomIso_apply l k p q (t.app n z) (𝟙 n) x

end SerrePositivity.InfinityCategories
