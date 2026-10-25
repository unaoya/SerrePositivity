module

public import SerrePositivity.KST.LocalizingInvariants.CochainCoconeTriangleMap
public import SerrePositivity.KST.LocalizingInvariants.ProLevelArrowTower
public import SerrePositivity.KST.LocalizingInvariants.ProGroupFiveTermZero
public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：実複体射の塔と、その元の mapping cone のホモロジー pro 判定を結ぶ。
方針：cone の全遷移と自然な接続射を構成し、実長完全列へ群の pro 判定を適用する。
規約：cone の次数別 pro 零性を一般 pro ∞ 圏の零対象性とは同一視しない。
使われ方：Tor 比較の実欠損から元の dg 代数射へ戻す K-8 e の抽象部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CochainProCone
open ProExcision
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 元の可換正方形に標準 cone 射を適用する関手。 -/
def coneFunctor : Arrow (Complex R) ⥤ Complex R where
  obj f := mappingCone f.hom
  map {f g} a := mappingCone.map f.hom g.hom a.left a.right a.w.symm
  map_id _ := mappingCone.map_id _
  map_comp _ _ := mappingCone.map_comp _ _ _ _ _ _ _ _ _

/-- cohomological な次数を保持する実ホモロジー群関手。 -/
def homologyGroups (n : ℤ) : Complex R ⥤ CommGrpCat.{u} :=
  homologyFunctor (ModuleCat R) (.up ℤ) n ⋙
    forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp

abbrev groupForget : ModuleCat.{u} R ⥤ CommGrpCat.{u} :=
  forget₂ (ModuleCat R) AddCommGrpCat ⋙ AddCommGrpCat.toCommGrp

variable {X Y : Tower (Complex R)} (f : LevelHom X Y)

/-- 元のレベル射と元の二つの遷移から作る cone の塔。 -/
def tower : Tower (Complex R) := (TowerDiagram.arrowTower f).map (coneFunctor R)

/-- 元の標的から実 cone への自然なホモロジー射。 -/
def inclusion (n : ℤ) :
    LevelHom (Y.map (homologyGroups R n)) ((tower R f).map (homologyGroups R n)) where
  app i := (groupForget R).map (homologyMap (mappingCone.inr (f.app i)) n)
  naturality h := by
    change (groupForget R).map (homologyMap (Y.transition h) n) ≫ _ =
      _ ≫ (groupForget R).map (homologyMap
        (mappingCone.map _ _ (X.transition h) (Y.transition h) (f.naturality h).symm) n)
    rw [← Functor.map_comp, ← Functor.map_comp, ← homologyMap_comp, ← homologyMap_comp]
    exact congrArg (fun t => (groupForget R).map (homologyMap t n))
      (mappingCone.triangleMap _ _ (X.transition h) (Y.transition h)
        (f.naturality h).symm).comm₂.symm

/-- 元の cone 三角形の接続射。隣接する二次数は指定した等式で照合する。 -/
def boundary (n m : ℤ) (hm : n + 1 = m) :
    LevelHom ((tower R f).map (homologyGroups R n)) (X.map (homologyGroups R m)) where
  app i := (groupForget R).map
    (homologyδOfTriangle (mappingCone.triangle (f.app i)) n m hm)
  naturality h := by
    have ht := cochainTriangleHomologyConnecting_naturality
      (mappingCone.triangleMap _ _ (X.transition h) (Y.transition h)
        (f.naturality h).symm) n m hm
    exact (Functor.map_comp (groupForget R) _ _).symm.trans
      ((congrArg (groupForget R).map ht).trans (Functor.map_comp (groupForget R) _ _))

/-- 同じ cone 三角形の第一の完全性。 -/
lemma exact_source (n m : ℤ) (hm : n + 1 = m) (i : ℕ)
    (x : (X.map (homologyGroups R m)).obj i) :
    ((f.map (homologyGroups R m)).app i).hom x = 1 ↔
      ∃ y, ((boundary R f n m hm).app i).hom y = x := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (homologyMap_exact₁_of_distTriang (mappingCone.triangle (f.app i))
      (DerivedCategory.mappingCone_triangle_distinguished _) n m hm) x

/-- 同じ cone 三角形の第二の完全性。 -/
lemma exact_target (n : ℤ) (i : ℕ) (x : (Y.map (homologyGroups R n)).obj i) :
    ((inclusion R f n).app i).hom x = 1 ↔
      ∃ y, ((f.map (homologyGroups R n)).app i).hom y = x := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (homologyMap_exact₂_of_distTriang (mappingCone.triangle (f.app i))
      (DerivedCategory.mappingCone_triangle_distinguished _) n) x

/-- 同じ cone 三角形の第三の完全性。 -/
lemma exact_cone (n m : ℤ) (hm : n + 1 = m) (i : ℕ)
    (x : ((tower R f).map (homologyGroups R n)).obj i) :
    ((boundary R f n m hm).app i).hom x = 1 ↔
      ∃ y, ((inclusion R f n).app i).hom y = x := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (homologyMap_exact₃_of_distTriang (mappingCone.triangle (f.app i))
      (DerivedCategory.mappingCone_triangle_distinguished _) n m hm) x

/-- 前の次数の cone が pro 零なら、元の射の核は eventual に消える。 -/
lemma map_eventuallyKernelTrivial (n : ℤ)
    (hprev : IsProZero ((tower R f).map (homologyGroups R (n - 1)))) :
    ProGroup.IsEventuallyKernelTrivial (f.map (homologyGroups R n)) :=
  ProGroup.eventuallyKernelTrivial_of_exact_proZero
    (boundary R f (n - 1) n (by omega)) (f.map (homologyGroups R n))
    (exact_source R f (n - 1) n (by omega)) hprev

/-- 同じ次数の cone が pro 零なら、元の射の像は eventual に全体を覆う。 -/
lemma map_eventuallyImageSurjective (n : ℤ)
    (hcurr : IsProZero ((tower R f).map (homologyGroups R n))) :
    ProGroup.IsEventuallyImageSurjective (f.map (homologyGroups R n)) :=
  ProGroup.eventuallyImageSurjective_of_exact_proZero
    (f.map (homologyGroups R n)) (inclusion R f n) (exact_target R f n) hcurr

/-- 隣接二次数の cone pro 零性から、元の比較射の pro 同型を得る。 -/
lemma map_isProIso (n : ℤ)
    (hprev : IsProZero ((tower R f).map (homologyGroups R (n - 1))))
    (hcurr : IsProZero ((tower R f).map (homologyGroups R n))) :
    IsProIso (f.map (homologyGroups R n)) :=
  ProGroup.proIso_of_fourTerm_exact_proZero
    (boundary R f (n - 1) n (by omega)) (f.map (homologyGroups R n)) (inclusion R f n)
    (exact_source R f (n - 1) n (by omega)) (exact_target R f n) hprev hcurr

/-- 元の射の隣接次数の像・核条件から、同じ実 cone の pro 零性を得る。 -/
lemma cone_isProZero_of_kernel_image (n : ℤ)
    (hcurr : ProGroup.IsEventuallyImageSurjective (f.map (homologyGroups R n)))
    (hnext : ProGroup.IsEventuallyKernelTrivial (f.map (homologyGroups R (n + 1)))) :
    IsProZero ((tower R f).map (homologyGroups R n)) :=
  ProGroup.proZero_of_fiveTerm_exact
    (f.map (homologyGroups R n)) (inclusion R f n)
    (boundary R f n (n + 1) rfl) (f.map (homologyGroups R (n + 1)))
    (exact_target R f n) (exact_cone R f n (n + 1) rfl)
    (exact_source R f n (n + 1) rfl)
    hcurr hnext

/-- 元の射の隣接二次数の pro 同型から、実 cone の pro 零性を得る。 -/
lemma cone_isProZero (n : ℤ)
    (hcurr : IsProIso (f.map (homologyGroups R n)))
    (hnext : IsProIso (f.map (homologyGroups R (n + 1)))) :
    IsProZero ((tower R f).map (homologyGroups R n)) :=
  cone_isProZero_of_kernel_image R f n
    (ProGroup.imageSurjective_of_proIso hcurr) (ProGroup.kernelTrivial_of_proIso hnext)

/-- 全整数次数で、実 cone の pro 零性と元の射の pro 同型は同値。 -/
lemma proZero_iff_map_isProIso :
    (∀ n : ℤ, IsProZero ((tower R f).map (homologyGroups R n))) ↔
      ∀ n : ℤ, IsProIso (f.map (homologyGroups R n)) :=
  ⟨fun h n => map_isProIso R f n (h (n - 1)) (h n),
    fun h n => cone_isProZero R f n (h n) (h (n + 1))⟩

end SerrePositivity.KST.LocalizingInvariants.CochainProCone
