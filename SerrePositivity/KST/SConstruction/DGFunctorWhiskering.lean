module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPrecomposition
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPostcomposition

/-! # 全次数 dg 関手圏上の厳密な前後合成
概要：元の Hom end 上の前後合成を、単位と縦合成を保つ dg 関手へ束ねる。
方針：全対象評価で元の同じ dg 合成保存と各評価式へ戻す。
規約：全次数 Hom を維持する。使われ方：dg 入力の高次 Hom と横合成への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] (B : Type t) [DGCategory A B]

/-- 実 dg 後合成は Hom end の元の閉単位を保つ。 -/
lemma dgFunctorHomPost_identity (H : DGFunctor A E B) (M : DGFunctor A D E) :
    dgFunctorIdentity A D E M ≫ dgFunctorHomPost A D E B H M M =
      dgFunctorIdentity A D B (M.comp H) := by
  apply dgFunctorHom_ext
  intro x
  rw [Category.assoc, dgFunctorHomPost_π, ← Category.assoc, dgFunctorIdentity_π,
    dgFunctorIdentity_π]
  exact H.map_id (M.obj x)

/-- 実 dg 後合成は Hom end の全次数の縦合成を保つ。 -/
lemma dgFunctorHomPost_composition (H : DGFunctor A E B) (M N P : DGFunctor A D E) :
    dgFunctorComposition A D E M N P ≫ dgFunctorHomPost A D E B H M P =
      (dgFunctorHomPost A D E B H M N ⊗ₘ dgFunctorHomPost A D E B H N P) ≫
        dgFunctorComposition A D B (M.comp H) (N.comp H) (P.comp H) := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgFunctorHomPost_π, dgFunctorComposition_π]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [dgFunctorHomPost_π]
  change dgFunctorComposition A D E M N P ≫
      (dgFunctorHomπ A D E M P x ≫ H.map (M.obj x) (P.obj x)) =
    ((dgFunctorHomπ A D E M N x ≫ H.map (M.obj x) (N.obj x)) ⊗ₘ
      (dgFunctorHomπ A D E N P x ≫ H.map (N.obj x) (P.obj x))) ≫
        eComp (Complex A) (H.obj (M.obj x)) (H.obj (N.obj x)) (H.obj (P.obj x))
  have hp := congrArg (fun k => k ≫ H.map (M.obj x) (P.obj x))
    (dgFunctorComposition_π A D E M N P x)
  exact ((Category.assoc _ _ _).symm.trans hp).trans (by
    rw [Category.assoc, H.map_comp, tensorHom_comp_tensorHom_assoc])

/-- 厳密 dg 後合成は、元の全次数 dg 関手圏の dg 関手。 -/
def dgFunctorPostDG (H : DGFunctor A E B) : DGFunctor A (DGFunctor A D E) (DGFunctor A D B) where
  obj M := M.comp H
  map M N := dgFunctorHomPost A D E B H M N
  map_id M := dgFunctorHomPost_identity A D E B H M
  map_comp M N P := dgFunctorHomPost_composition A D E B H M N P

variable [Small.{u} B]

/-- 実 dg 前合成は Hom end の元の閉単位を保つ。 -/
lemma dgFunctorHomPre_identity (H : DGFunctor A B D) (M : DGFunctor A D E) :
    dgFunctorIdentity A D E M ≫ dgFunctorHomPre A D E B H M M =
      dgFunctorIdentity A B E (H.comp M) := by
  apply dgFunctorHom_ext
  intro x
  rw [Category.assoc, dgFunctorHomPre_π, dgFunctorIdentity_π, dgFunctorIdentity_π]
  rfl

/-- 実 dg 前合成は Hom end の全次数の縦合成を保つ。 -/
lemma dgFunctorHomPre_composition (H : DGFunctor A B D) (M N P : DGFunctor A D E) :
    dgFunctorComposition A D E M N P ≫ dgFunctorHomPre A D E B H M P =
      (dgFunctorHomPre A D E B H M N ⊗ₘ dgFunctorHomPre A D E B H N P) ≫
        dgFunctorComposition A B E (H.comp M) (H.comp N) (H.comp P) := by
  apply dgFunctorHom_ext
  intro x
  simp only [Category.assoc, dgFunctorHomPre_π, dgFunctorComposition_π]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [dgFunctorHomPre_π]
  rfl

/-- 厳密 dg 前合成は、元の全次数 dg 関手圏の dg 関手。 -/
def dgFunctorPreDG (H : DGFunctor A B D) : DGFunctor A (DGFunctor A D E) (DGFunctor A B E) where
  obj M := H.comp M
  map M N := dgFunctorHomPre A D E B H M N
  map_id M := dgFunctorHomPre_identity A D E B H M
  map_comp M N P := dgFunctorHomPre_composition A D E B H M N P

end SerrePositivity.KST.SConstruction
