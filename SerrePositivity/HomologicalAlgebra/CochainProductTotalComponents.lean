module
public import SerrePositivity.HomologicalAlgebra.CochainProductTotalizationHomotopy
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
概要：非負余鎖次数の任意の二重複体の積全複体を、指定成分の積として表示する。
方針：整数への零延長の行同型を使い、負の行を零として積射影の普遍性を戻す。
規約：余単体図式に限らず、Moore 正規化後の重みの end にも適用する。
使われ方：HA 1.2.4、G10 の線形 end と Hom 複体の成分比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SerrePositivity.DifferentialGraded
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.CochainProductTotal
variable {A : Type u} [CommRing A]

/-- 零延長後の非負横次数の行を、元の横余鎖的複体へ戻す指定同型。 -/
def rowIso (X : CochainComplex (Complex A) ℕ) (n : ℕ) :
    (X.extend ComplexShape.embeddingUpNat).X (n : ℤ) ≅ X.X n :=
  X.extendXIso
    ComplexShape.embeddingUpNat (i := n) rfl

/-- 全次数 q の指定 n 成分への射影。 -/
def componentπ (X : CochainComplex (Complex A) ℕ) (n : ℕ) (q : ℤ) :
    ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj X).X q ⟶ (X.X n).X (q-n) :=
  SerrePositivity.HomologicalAlgebra.ProductTotal.π
    (X.extend ComplexShape.embeddingUpNat) n (q-n) q (by omega) ≫
      (rowIso X n).hom.f (q-n)

/-- 非負横次数の指定同型は元の図式の射と可換。 -/
@[reassoc]
theorem rowIso_naturality {X Y : CochainComplex (Complex A) ℕ} (f : X ⟶ Y) (n : ℕ) :
    ((HomologicalComplex.extendMap f ComplexShape.embeddingUpNat).f n) ≫ (rowIso Y n).hom =
      (rowIso X n).hom ≫ f.f n := by
  rw [HomologicalComplex.extendMap_f
    f ComplexShape.embeddingUpNat
    (i := n) (i' := (n : ℤ)) rfl]
  simp [rowIso]

/-- 同じ積 total 関手の射は、各元の横余鎖成分への射影と厳密に可換。 -/
@[reassoc]
theorem componentπ_naturality {X Y : CochainComplex (Complex A) ℕ} (f : X ⟶ Y)
    (n : ℕ) (q : ℤ) :
    ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).map f).f q ≫ componentπ Y n q =
      componentπ X n q ≫ (f.f n).f (q-n) := by
  dsimp only [componentπ, cochainProductTotalizationFunctor, Functor.comp_map]
  erw [← Category.assoc, SerrePositivity.HomologicalAlgebra.ProductTotal.map_π,
    Category.assoc]
  erw [← HomologicalComplex.comp_f, rowIso_naturality, HomologicalComplex.comp_f]
  rfl

/-- 零延長で入れた負の行は零複体。 -/
theorem negativeRow_isZero (X : CochainComplex (Complex A) ℕ) (a : ℤ) (ha : a < 0) :
    Limits.IsZero ((X.extend ComplexShape.embeddingUpNat).X a) :=
  X.isZero_extend_X
    ComplexShape.embeddingUpNat a (fun n hn => by change (n : ℤ) = a at hn; omega)

/-- 元の非負横余鎖次数の成分だけで、積全複体への次数ごとの射を判定できる。 -/
theorem component_hom_ext (X : CochainComplex (Complex A) ℕ) {M : ModuleCat.{u} A} (q : ℤ)
    {f g : M ⟶ ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj X).X q}
    (h : ∀ n, f ≫ componentπ X n q = g ≫ componentπ X n q) : f = g := by
  apply SerrePositivity.HomologicalAlgebra.ProductTotal.hom_ext
    (X.extend ComplexShape.embeddingUpNat) q
  intro a b hab
  by_cases ha : 0 ≤ a
  · lift a to ℕ using ha
    have hb : b = q - (a : ℤ) := by omega
    subst b
    apply (cancel_mono ((rowIso X a).hom.f (q-a))).mp
    simpa only [componentπ, Category.assoc] using h a
  · exact ((HomologicalComplex.eval _ _ b).map_isZero
      (negativeRow_isZero X a (by omega))).eq_of_tgt _ _


/-- 元の非負横余鎖成分の族から、同じ積全複体の全次数 q への射を作る。 -/
def componentLift (X : CochainComplex (Complex A) ℕ) {M : ModuleCat.{u} A} (q : ℤ)
    (f : ∀ n : ℕ, M ⟶ (X.X n).X (q-n)) :
    M ⟶ ((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj X).X q :=
  SerrePositivity.HomologicalAlgebra.ProductTotal.lift
    (X.extend ComplexShape.embeddingUpNat) q (fun a b hab =>
      if ha : 0 ≤ a then
        f a.toNat ≫ (rowIso X a.toNat).inv.f (q-a.toNat) ≫
          eqToHom (by rw [Int.toNat_of_nonneg ha]; congr 1; omega)
      else 0)

@[reassoc (attr := simp)]
theorem componentLift_π (X : CochainComplex (Complex A) ℕ) {M : ModuleCat.{u} A} (q : ℤ)
    (f : ∀ n : ℕ, M ⟶ (X.X n).X (q-n)) (n : ℕ) :
    componentLift X q f ≫ componentπ X n q = f n := by
  dsimp only [componentLift, componentπ]
  rw [← Category.assoc, SerrePositivity.HomologicalAlgebra.ProductTotal.lift_π]
  simp only [Int.natCast_nonneg, dite_true, Int.toNat_natCast]
  simp

/-- 頂点を変えず、元の横余鎖成分への指定射影を持つ積錐。 -/
def componentFan (X : CochainComplex (Complex A) ℕ) (q : ℤ) :
    Fan (fun n : ℕ => (X.X n).X (q-n)) :=
  Fan.mk (((cochainProductTotalizationFunctor (ModuleCat.{u} A)).obj X).X q) (componentπ X · q)

/-- 積全複体の次数 q は、指定射影に関して ∏ n≥0, Xⁿ[q−n] そのもの。 -/
def componentFanIsLimit (X : CochainComplex (Complex A) ℕ) (q : ℤ) :
    IsLimit (componentFan X q) :=
  Fan.IsLimit.mk _
    (fun s => componentLift X q (fun n => s.π.app ⟨n⟩))
    (by intro s n; exact componentLift_π X q _ n)
    (by intro s m hm; apply component_hom_ext X q; intro n; rw [componentLift_π]; exact hm n)


end SerrePositivity.HomologicalAlgebra.CochainProductTotal
