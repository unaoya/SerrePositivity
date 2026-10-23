module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CorePullbackMap

/-!
概要：inner fibration に沿う引き戻しと core の厳密な交換同型。
方針：包含の単射性と二射影で比較射の二つの逆条件を確認する。
規約：同型の順方向は標準の corePullbackMap を保持する。
使われ方：Cat_∞ の引き戻しの全試験対象の関手 core の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

variable {E F B : SSet.{u}}

/-- 概要：core の引き戻しからの基礎写像は第一射影を保つ。
方針：元の引き戻しの lift の第一射影を計算する。
規約：core の包含との合成を明示する。
使われ方：比較の第一成分の逆条件。 -/
@[reassoc] lemma corePullbackUnderlying_fst (p : E ⟶ B) (q : F ⟶ B) :
    corePullbackUnderlying p q ≫ pullback.fst p q =
      pullback.fst (quasicategoryCoreMap p) (quasicategoryCoreMap q) ≫ (quasicategoryCore E).ι :=
  pullback.lift_fst ..

/-- 概要：core の引き戻しからの基礎写像は第二射影を保つ。
方針：元の引き戻しの lift の第二射影を計算する。
規約：core の包含との合成を明示する。
使われ方：比較の第二成分の逆条件。 -/
@[reassoc] lemma corePullbackUnderlying_snd (p : E ⟶ B) (q : F ⟶ B) :
    corePullbackUnderlying p q ≫ pullback.snd p q =
      pullback.snd (quasicategoryCoreMap p) (quasicategoryCoreMap q) ≫ (quasicategoryCore F).ι :=
  pullback.lift_snd ..

/-- 概要：標準の core の比較の第一成分は元の第一射影の core。
方針：core 側の lift の第一射影を計算する。
規約：単体集合として厳密な等式。
使われ方：全試験関手 core の第一射影。 -/
@[reassoc] lemma corePullbackMap_fst (p : E ⟶ B) (q : F ⟶ B) :
    corePullbackMap p q ≫ pullback.fst (quasicategoryCoreMap p) (quasicategoryCoreMap q) =
      quasicategoryCoreMap (pullback.fst p q) := pullback.lift_fst ..

/-- 概要：標準の core の比較の第二成分は元の第二射影の core。
方針：core 側の lift の第二射影を計算する。
規約：単体集合として厳密な等式。
使われ方：全試験関手 core の第二射影。 -/
@[reassoc] lemma corePullbackMap_snd (p : E ⟶ B) (q : F ⟶ B) :
    corePullbackMap p q ≫ pullback.snd (quasicategoryCoreMap p) (quasicategoryCoreMap q) =
      quasicategoryCoreMap (pullback.snd p q) := pullback.lift_snd ..

/-- 概要：core への逆向き比較を含めると元の基礎写像に戻る。
方針：core への持ち上げの包含を計算する。
規約：元の二つの射影への作用を変えない。
使われ方：比較の二つの逆条件での包含の消去。 -/
@[reassoc] lemma corePullbackInv_ι [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] :
    corePullbackInv p q ≫ (quasicategoryCore (pullback p q)).ι = corePullbackUnderlying p q := rfl

/-- 概要：inner fibration に沿う引き戻しの core は二つの core の引き戻しと同型。
方針：包含へ合成して二射影で両方の逆条件を比較する。
規約：第一関手の inner fibration 性だけを仮定し、第二関手は任意。
使われ方：関手 core の全次数での引き戻し表示。 -/
def corePullbackIso [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration p] :
    (quasicategoryCore (pullback p q) : SSet.{u}) ≅
      pullback (quasicategoryCoreMap p) (quasicategoryCoreMap q) where
  hom := corePullbackMap p q
  inv := corePullbackInv p q
  hom_inv_id := by
    apply (cancel_mono (quasicategoryCore (pullback p q)).ι).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, corePullbackInv_ι_assoc, corePullbackUnderlying_fst,
        corePullbackMap_fst_assoc, quasicategoryCoreMap_ι, Category.id_comp]
    · simp only [Category.assoc, corePullbackInv_ι_assoc, corePullbackUnderlying_snd,
        corePullbackMap_snd_assoc, quasicategoryCoreMap_ι, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply (cancel_mono (quasicategoryCore E).ι).mp
      simp only [Category.assoc, corePullbackMap_fst_assoc, quasicategoryCoreMap_ι,
        corePullbackInv_ι_assoc, corePullbackUnderlying_fst, Category.id_comp]
    · apply (cancel_mono (quasicategoryCore F).ι).mp
      simp only [Category.assoc, corePullbackMap_snd_assoc, quasicategoryCoreMap_ι,
        corePullbackInv_ι_assoc, corePullbackUnderlying_snd, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
