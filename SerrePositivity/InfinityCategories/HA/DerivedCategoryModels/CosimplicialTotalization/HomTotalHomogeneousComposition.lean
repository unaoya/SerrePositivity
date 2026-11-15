module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.HomTotalNaturality

/-!
# 積 Hom–Tot 成分と任意次数の合成

概要：元の積射影によるHom成分は任意の斉次Homパラメータとの合成を保つ。
方針：同じcochain成分の評価と合成の結合則を使う。
規約：次数零の鎖射に限らない。IS-W2 B02の同じ全単体照合の分割。
使われ方：HA 1.2.4、実標準AWとHom–Tot比較の成分の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 概要：指定Hom成分は任意次数の前合成を保持する。
方針：全次数成分で同じ積射影と結合則を使う。
規約：p・qは任意の整数。使われ方：HA 1.2.4 の全Hom単体の成分照合。 -/
theorem homTotalComponent_homogeneous_comp {P Q : Complex A}
    (X : CosimplicialObject (Complex A)) (p q : ℤ) (n : ℕ)
    (f : Homogeneous P Q p) (g : Homogeneous Q ((productTotalFunctor A).obj X) q) :
    homTotalComponent P X (p + q) n (f.comp g rfl) =
      f.comp (homTotalComponent Q X q n g) (by omega) := by
  apply Cochain.ext
  intro i j hij
  have hj : j = i + (p + q) - n := by omega
  cases hj
  rw [homTotalComponent_v,
    Cochain.comp_v f g rfl i (i + p) (i + (p + q)) rfl (by omega),
    Cochain.comp_v f (homTotalComponent Q X q n g) (by omega)
      i (i + p) (i + (p + q) - n) rfl (by omega)]
  have hv := homTotalComponent_v Q X q n g (i + p)
  have hv' : (homTotalComponent Q X q n g).v (i + p) (i + (p + q) - n) (by omega) =
      g.v (i + p) (i + (p + q)) (by omega) ≫ componentπ X n (i + (p + q)) := by
    convert hv using 1 <;> (repeat' first | omega | congr! 1)
  rw [hv']
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
