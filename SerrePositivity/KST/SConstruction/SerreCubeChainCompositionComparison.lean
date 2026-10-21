module
public import SerrePositivity.KST.SConstruction.SerreCubeComplexDimensionComparison
public import SerrePositivity.KST.SConstruction.SerreCubeTopCompositionImage

/-! # 元の Serre 分割合成と端点・次元の比較
概要：元の鎖射の次元移送と、元の Serre tensor 分割・dg 合成の異種等号を扱う。
方針：元の端点と次元の等号を消去し、実鎖射の等号に戻す。
規約：元の tensor 順と dg 合成を保持。使われ方：一面の左右生成射の正規化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の同じ次元等号の移送の前合成は、元の実鎖射と異種等号で一致する。 -/
lemma serreCubeChain_precomp_heq {p q : ℕ} (h : p = q) {K : Complex A}
    (f : serreCubeComplex A q ⟶ K) :
    HEq (eqToHom (congrArg (serreCubeComplex A) h) ≫ f) f := by
  cases h
  exact heq_of_eq (Category.id_comp f)

/-- 元の始域次元が等しい鎖射の異種等号を、元の移送を前合成した厳密な等号へ戻す。 -/
lemma serreCubeChain_eq_transport_of_heq {p q : ℕ} (h : p = q) {K : Complex A}
    (f : serreCubeComplex A p ⟶ K) (g : serreCubeComplex A q ⟶ K) (hf : HEq f g) :
    f = eqToHom (congrArg (serreCubeComplex A) h) ≫ g := by
  cases h
  rw [eqToHom_refl, Category.id_comp]
  exact eq_of_heq hf

/-- 元の Serre 分割と二つの Hom 鎖射からの、同じ因子順の実 dg 合成。 -/
def serreCubeChainComposition {D : Type v} [DGCategory A D] {x y z : D} (p q : ℕ)
    (f : serreCubeComplex A p ⟶ homObject A D x y)
    (g : serreCubeComplex A q ⟶ homObject A D y z) :
    serreCubeComplex A (p + q) ⟶ homObject A D x z :=
  (serreCubeTensorIso A p q).hom.hom ≫ (f ⊗ₘ g) ≫ eComp (Complex A) x y z

/-- 元の端点・次元と両鎖射の比較は、元の同じ実 Serre 分割合成に伝播する。 -/
lemma serreCubeChainComposition_heq {D : Type v} [DGCategory A D]
    {x y z x' y' z' : D} (hx : x = x') (hy : y = y') (hz : z = z')
    {p q p' q' : ℕ} (hp : p = p') (hq : q = q')
    (f : serreCubeComplex A p ⟶ homObject A D x y)
    (g : serreCubeComplex A q ⟶ homObject A D y z)
    (f' : serreCubeComplex A p' ⟶ homObject A D x' y')
    (g' : serreCubeComplex A q' ⟶ homObject A D y' z') (hf : HEq f f') (hg : HEq g g') :
    HEq (serreCubeChainComposition A p q f g) (serreCubeChainComposition A p' q' f' g') := by
  cases hx
  cases hy
  cases hz
  cases hp
  cases hq
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

end SerrePositivity.KST.SConstruction
