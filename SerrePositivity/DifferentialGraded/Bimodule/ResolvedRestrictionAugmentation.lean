module
public import SerrePositivity.DifferentialGraded.Bimodule.MiddleRightRestrictionCoherence
public import SerrePositivity.DifferentialGraded.Bimodule.QuasiIso

/-! # 二段階の制限後bimoduleモデルの増大を合成する

## 概要
二段階の制限後bimoduleモデルの増大を合成する。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (L : Type t) [DGCategory A L]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段目の増大をさらに制限し、合成制限の表示へ送る射。 -/
def middleRightRestrictionCompositeMap
    {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) :
    (middleRightRestrictionFunctor A E D L F).obj R ⟶
      (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q :=
  (middleRightRestrictionFunctor A E D L F).map q ≫
    (middleRightRestrictionCompObjIso A D L E T F G Q).hom

@[simp]
lemma middleRightRestrictionCompositeMap_value
    {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (middleRightRestrictionCompositeMap A D E T L F G q) =
      (valueEvaluation A E L (F.obj d) l).map q := by
  simp only [middleRightRestrictionCompositeMap, CategoryTheory.Functor.map_comp,
    middleRightRestrictionCompObjIso_hom_value, Category.comp_id]
  exact middleRightRestrictionMap_value_eval A E D L F q d l

lemma middleRightRestrictionCompositeMap_quasiIso
    {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) (hq : quasiIso A E L q) :
    quasiIso A D L (middleRightRestrictionCompositeMap A D E T L F G q) := by
  intro d l
  rw [middleRightRestrictionCompositeMap_value]
  exact hq (F.obj d) l

/-- 二つの増大を、合成関手の右制限への増大へまとめる。 -/
def resolvedRestrictionAugmentationComp
    {S : BimoduleCategory A D L} {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (r : S ⟶ (middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) :
    S ⟶ (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q :=
  r ≫ (middleRightRestrictionFunctor A E D L F).map q ≫
    (middleRightRestrictionCompObjIso A D L E T F G Q).hom

@[simp]
lemma resolvedRestrictionAugmentationComp_value
    {S : BimoduleCategory A D L} {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (r : S ⟶ (middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (resolvedRestrictionAugmentationComp A D E T L F G r q) =
      (valueEvaluation A D L d l).map r ≫ (valueEvaluation A E L (F.obj d) l).map q := by
  simp only [resolvedRestrictionAugmentationComp, CategoryTheory.Functor.map_comp,
    middleRightRestrictionCompObjIso_hom_value, Category.comp_id]
  exact congrArg (fun k => (valueEvaluation A D L d l).map r ≫ k)
    (middleRightRestrictionMap_value_eval A E D L F q d l)

lemma resolvedRestrictionAugmentationComp_quasiIso
    {S : BimoduleCategory A D L} {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (r : S ⟶ (middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q)
    (hr : quasiIso A D L r) (hq : quasiIso A E L q) :
    quasiIso A D L (resolvedRestrictionAugmentationComp A D E T L F G r q) := by
  intro d l
  rw [resolvedRestrictionAugmentationComp_value]
  have : QuasiIso ((valueEvaluation A D L d l).map r) := hr d l
  have : QuasiIso ((valueEvaluation A E L (F.obj d) l).map q) := hq (F.obj d) l
  exact quasiIso_comp _ _

/-- 恒等右制限への指定増大を、元のbimoduleへの射として読む。 -/
def resolvedRestrictionAugmentationId {S Q : BimoduleCategory A D L}
    (q : S ⟶ (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) : S ⟶ Q :=
  q ≫ (middleRightRestrictionIdObjIso A D L Q).hom

@[simp]
lemma resolvedRestrictionAugmentationId_value {S Q : BimoduleCategory A D L}
    (q : S ⟶ (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (resolvedRestrictionAugmentationId A D L q) =
      (valueEvaluation A D L d l).map q := by
  rw [resolvedRestrictionAugmentationId, CategoryTheory.Functor.map_comp,
    middleRightRestrictionIdObjIso_hom_value, Category.comp_id]

lemma resolvedRestrictionAugmentationId_quasiIso {S Q : BimoduleCategory A D L}
    (q : S ⟶ (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q)
    (hq : quasiIso A D L q) : quasiIso A D L (resolvedRestrictionAugmentationId A D L q) := by
  intro d l
  rw [resolvedRestrictionAugmentationId_value]
  exact hq d l

end SerrePositivity.DifferentialGraded.BimoduleCategory
