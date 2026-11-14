module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ProductCone

/-!
概要：積全複体の対角線に一つだけ非零成分がある場合の、指定射影による同型。
方針：同じ積錐の lift と射影の判定を用い、他の成分の零性で逆射を検証する。
規約：同型の前向きの射を元の componentπ に固定する。
使われ方：HA 1.2.4、G10 の離散加群入力と交代余面複体の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SerrePositivity.DifferentialGraded
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 指定された一つの余単体成分から、他を零として積全次数へ送る射。 -/
def singleComponentLift (X : CosimplicialObject (Complex A)) (q : ℤ) (n : ℕ) :
    (X.obj ⦋n⦌).X (q-n) ⟶ ((productTotalFunctor A).obj X).X q :=
  componentLift X q (fun m => if h : m=n then eqToHom (by subst m; rfl) else 0)

@[reassoc (attr := simp)]
theorem singleComponentLift_π (X : CosimplicialObject (Complex A)) (q : ℤ) (n : ℕ) :
    singleComponentLift X q n ≫ componentπ X n q = 𝟙 _ := by
  simp [singleComponentLift]

/-- 他の余単体成分がすべて零なら、元の指定射影が同型になる。 -/
def singleComponentIso (X : CosimplicialObject (Complex A)) (q : ℤ) (n : ℕ)
    (hz : ∀ m : ℕ, m≠n → IsZero ((X.obj ⦋m⦌).X (q-m))) :
    ((productTotalFunctor A).obj X).X q ≅ (X.obj ⦋n⦌).X (q-n) where
  hom := componentπ X n q
  inv := singleComponentLift X q n
  hom_inv_id := by
    apply component_hom_ext X q
    intro m
    by_cases h : m=n
    · subst m
      simp [Category.assoc]
    · exact (hz m h).eq_of_tgt _ _
  inv_hom_id := singleComponentLift_π X q n

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
