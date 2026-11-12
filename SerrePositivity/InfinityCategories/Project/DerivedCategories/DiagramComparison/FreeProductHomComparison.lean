module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom

/-!
概要：積重みと正規化テンソルの指定二射を、全単体 Hom の比較にする。
方針：余単体図式からの Hom 関手に同じ AW・shuffle を前合成する。
規約：標的の全図式射と単体作用素を保つ。空間の同値性は別途証明する。
使われ方：HA 1.2.4、G10 の正規化 Hom と積重みの切断空間の比較。
-/
@[expose] public noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (X : J ⥤ SSet.{u}) (P : SimplexCategory ⥤ (J ⥤ SSet.{u}))
variable (φ : simplicialRingCoefficient.{u} →+* A)

/-- 指定 AW の前合成による、標的にも自然な全単体 Hom 比較。 -/
def freeProductHomComparison :
    cosimplicialHom (freeTensorFrame A X P) ⟶ cosimplicialHom (freeProductFrame A X P) :=
  cosimplicialHomMap (freeProductFrameAW A X P φ)

/-- 指定 shuffle の前合成による逆向きの全単体射。 -/
def freeProductHomReverse :
    cosimplicialHom (freeProductFrame A X P) ⟶ cosimplicialHom (freeTensorFrame A X P) :=
  cosimplicialHomMap (freeProductFrameShuffle A X P φ)

/-- 比較の全次数での作用は、同じ図式 AW の前合成である。 -/
theorem freeProductHomComparison_apply (H : J ⥤ CochainComplex (ModuleCat A) ℤ)
    (n : SimplexCategoryᵒᵖ) (f : (freeTensorFrame A X P).obj n.unop ⟶ H) :
    ((freeProductHomComparison A X P φ).app H).app n f =
      freeProductDiagramAW φ X (P.obj n.unop) ≫ f := rfl

/-- 逆向きの作用も同じ図式 shuffle の前合成である。 -/
theorem freeProductHomReverse_apply (H : J ⥤ CochainComplex (ModuleCat A) ℤ)
    (n : SimplexCategoryᵒᵖ) (f : (freeProductFrame A X P).obj n.unop ⟶ H) :
    ((freeProductHomReverse A X P φ).app H).app n f =
      freeProductDiagramShuffle φ X (P.obj n.unop) ≫ f := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
