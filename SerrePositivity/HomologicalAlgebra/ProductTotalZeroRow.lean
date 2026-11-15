module
public import SerrePositivity.HomologicalAlgebra.ProductTotal

/-!
概要：負の第一行からの微分が零の二重複体で、積全複体から零行への標準鎖写像を作る。
方針：積全微分の成分公式で横微分の項を消す。
規約：非有界縦次数を許し、零行への指定射影をそのまま使う。
使われ方：HA 1.2.4、G10 の余単体次数零への標準脚。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]

/-- 零行への指定射影が鎖写像となるための微分の等式。 -/
theorem zeroRow_d (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hK : K.d (-1) 0 = 0) (q : ℤ) :
    ((functor C).obj K).d q (q+1) ≫ π K 0 (q+1) (q+1) (by omega) =
      π K 0 q q (by omega) ≫ (K.X 0).d q (q+1) := by
  have h := d_π K 0 (q+1) q (by omega)
  have hh (b : ℤ) (hb : b=q) :
      π K 0 b q (by omega) ≫ (K.X 0).d b (q+1) =
        π K 0 q q (by omega) ≫ (K.X 0).d q (q+1) := by
    subst b
    rfl
  refine Eq.trans ?_ (hh (q+1-1) (by omega))
  simpa [hK] using h

/-- 積全複体から零行への標準鎖写像。 -/
def zeroRowHom (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hK : K.d (-1) 0 = 0) : (functor C).obj K ⟶ K.X 0 where
  f q := π K 0 q q (by omega)
  comm' q r hqr := by
    have hr : q+1=r := hqr
    subst r
    exact (zeroRow_d K hK q).symm

/-- 標準零行射影は、同じ二重複体の射に自然。 -/
theorem zeroRowHom_naturality {K L : HomologicalComplex₂ C (.up ℤ) (.up ℤ)}
    (f : K ⟶ L) (hK : K.d (-1) 0 = 0) (hL : L.d (-1) 0 = 0) :
    (functor C).map f ≫ zeroRowHom L hL = zeroRowHom K hK ≫ f.f 0 := by
  ext q
  exact map_π f 0 q q (by omega)

end SerrePositivity.HomologicalAlgebra.ProductTotal
