module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
# 実現の各次数の元の行の余積

## 概要
直和全複体の各次数を、元の単体次数の行の同じ余積として記述する。

## 方針
非正の横次数を自然数へ戻し、正の行の零性と totalDesc で普遍性を示す。

## 規約
内部次数は非有界。同じ標準行の包含を余積の脚に用いる。

## 使われ方
HA 1.2.4。実 coherent bar 比較の各次数での逆射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 非正の行を元の自然数次数の同じ行へ戻す。 -/
def realizationRowAtIso (X : SimplicialObject (Complex A)) (a : ℤ) (ha : a ≤ 0) :
    ((doubleComplexFunctor A).obj X).X a ≅ X.obj (op ⦋(-a).toNat⦌) :=
  (AlternatingFaceMapComplex.obj X).extendXIso SerrePositivity.embUp (by
    change (0 : ℤ) - (((-a).toNat : ℕ) : ℤ) = a
    rw [Int.toNat_of_nonneg (by omega)]
    omega)

/-- 元の各行の標準包含で指定する次数 q の余積候補。 -/
def realizationDegreeCofan (X : SimplicialObject (Complex A)) (q : ℤ) :
    Cofan (fun n : ℕ => (X.obj (op ⦋n⦌)).X (q + (n : ℤ))) :=
  Cofan.mk (((directSumTotalFunctor A).obj X).X q) (fun n =>
    (standardRowCochain A X n).v (q + (n : ℤ)) q (by omega))

/-- 任意の行ごとの射を totalDesc により同じ全次数からの射へまとめる。 -/
def realizationDegreeDesc (X : SimplicialObject (Complex A)) (q : ℤ) (M : ModuleCat.{u} A)
    (f : ∀ n : ℕ, (X.obj (op ⦋n⦌)).X (q + (n : ℤ)) ⟶ M) :
    ((directSumTotalFunctor A).obj X).X q ⟶ M :=
  ((doubleComplexFunctor A).obj X).totalDesc (fun a b h =>
    if ha : a ≤ 0 then
      (realizationRowAtIso A X a ha).hom.f b ≫
        ((X.obj (op ⦋(-a).toNat⦌)).XIsoOfEq (show b = q + (((-a).toNat : ℕ) : ℤ) by
          have hn : (((-a).toNat : ℕ) : ℤ) = -a := Int.toNat_of_nonneg (by omega)
          change a + b = q at h
          omega)).hom ≫ f (-a).toNat
    else 0)

/-- 各元の行への制限は、最初に指定した同じ射になる。 -/
@[reassoc]
theorem realizationDegreeDesc_fac (X : SimplicialObject (Complex A)) (q : ℤ) (M : ModuleCat.{u} A)
    (f : ∀ n : ℕ, (X.obj (op ⦋n⦌)).X (q + (n : ℤ)) ⟶ M) (n : ℕ) :
    (realizationDegreeCofan A X q).inj n ≫ realizationDegreeDesc A X q M f = f n := by
  change (standardRowCochain A X n).v (q + (n : ℤ)) q (by omega) ≫ _ = _
  rw [standardRowCochain_v]
  unfold realizationDegreeDesc
  rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
  simp only [show -(n : ℤ) ≤ 0 by omega, dite_true]
  have hgen (m : ℕ) (hm : SerrePositivity.embUp.f m = -(n : ℤ))
      (hb : q + (n : ℤ) = q + (m : ℤ)) :
      (doubleComplexRowIso A X n).inv.f (q + (n : ℤ)) ≫
        (((AlternatingFaceMapComplex.obj X).extendXIso SerrePositivity.embUp hm).hom.f
          (q + (n : ℤ)) ≫ ((X.obj (op ⦋m⦌)).XIsoOfEq hb).hom) ≫ f m = f n := by
    have hmn : m = n := by
      change (0 : ℤ) - (m : ℤ) = -(n : ℤ) at hm
      omega
    subst m
    change (doubleComplexRowIso A X n).inv.f (q + (n : ℤ)) ≫
      ((doubleComplexRowIso A X n).hom.f (q + (n : ℤ)) ≫ 𝟙 _) ≫ f n = _
    simp only [Category.comp_id]
    exact Iso.inv_hom_id_assoc
      ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) (q + (n : ℤ))).mapIso
        (doubleComplexRowIso A X n)) (f n)
  exact hgen _ _ _

/-- 各次数で、元のすべての行の標準包含は余積を与える。 -/
def realizationDegreeCofan_isColimit (X : SimplicialObject (Complex A)) (q : ℤ) :
    IsColimit (realizationDegreeCofan A X q) := by
  refine Cofan.IsColimit.mk _
    (fun c => realizationDegreeDesc A X q c.pt c.inj)
    (fun c n => realizationDegreeDesc_fac A X q c.pt c.inj n) ?_
  intro c m hm
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  by_cases ha : a ≤ 0
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, -(n : ℤ) = a := by
      refine ⟨(-a).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    have hb : b = q + (n : ℤ) := by change -(n : ℤ) + b = q at hab; omega
    subst b
    have he := (hm n).trans (realizationDegreeDesc_fac A X q c.pt c.inj n).symm
    change (standardRowCochain A X n).v (q + (n : ℤ)) q (by omega) ≫ m =
      (standardRowCochain A X n).v (q + (n : ℤ)) q (by omega) ≫ _ at he
    rw [standardRowCochain_v, Category.assoc, Category.assoc] at he
    exact (cancel_epi ((doubleComplexRowIso A X n).inv.f (q + (n : ℤ)))).mp he
  · have hz : IsZero (((doubleComplexFunctor A).obj X).X a) :=
      HomologicalComplex.isZero_extend_X (AlternatingFaceMapComplex.obj X)
        SerrePositivity.embUp a (fun n hn => by
          change (0 : ℤ) - (n : ℤ) = a at hn
          omega)
    exact ((HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) b).map_isZero hz).eq_of_src _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
