module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCompositionImage
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 元の分割最高生成元像と厳密 dg 関手
概要：元の tensor 分割・豊穣合成の最高生成元像を、実 dg 関手の値でも回収する。
方針：元の dg 合成保存と tensor 射の合成則を、元の最高生成元評価に適用する。
規約：元の実鎖射と通常順合成を保持。使われ方：native HA 成分の分割合成像。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
variable {C : Type v} {D : Type w} [DGCategory A C] [DGCategory A D]

/-- 元の二つの Hom 鎖射と dg 合成保存の、元の tensor 付き可換式。 -/
lemma dgFunctorTensorPair_composition (F : DGFunctor A C D) {x y z : C}
    {P Q : Complex A} (f : P ⟶ (x ⟶[Complex A] y)) (g : Q ⟶ (y ⟶[Complex A] z)) :
    (f ⊗ₘ g) ≫ eComp (Complex A) x y z ≫ F.map x z =
      ((f ≫ F.map x y) ⊗ₘ (g ≫ F.map y z)) ≫
        eComp (Complex A) (F.obj x) (F.obj y) (F.obj z) := by
  rw [F.map_comp, ← Category.assoc, tensorHom_comp_tensorHom]

/-- 元の分割・両 Hom 射・豊穣合成は、元の実 dg 関手による後合成と可換。 -/
lemma serreCubeComposition_post (F : DGFunctor A C D) {x y z : C} (p q : ℕ)
    (f : serreCubeComplex A p ⟶ homObject A C x y)
    (g : serreCubeComplex A q ⟶ homObject A C y z) :
    ((serreCubeTensorIso A p q).hom.hom ≫ (f ⊗ₘ g) ≫ eComp (Complex A) x y z) ≫
        F.map x z =
      (serreCubeTensorIso A p q).hom.hom ≫
        ((f ≫ F.map x y) ⊗ₘ (g ≫ F.map y z)) ≫
          eComp (Complex A) (F.obj x) (F.obj y) (F.obj z) := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun h => (serreCubeTensorIso A p q).hom.hom ≫ h)
      ((Category.assoc _ _ _).trans (dgFunctorTensorPair_composition A F f g)))

/-- 元の実 dg 関手の値における分割最高生成元像は、同じ通常順合成を回収する。 -/
lemma serreCubeTopCellImage_composition_post (F : DGFunctor A C D) {x y z : C} (p q : ℕ)
    (f : serreCubeComplex A p ⟶ homObject A C x y)
    (g : serreCubeComplex A q ⟶ homObject A C y z) :
    serreCubeTopCellImage A (homObject A D (F.obj x) (F.obj z)) (p + q)
        (((serreCubeTensorIso A p q).hom.hom ≫ (f ⊗ₘ g) ≫ eComp (Complex A) x y z) ≫
          F.map x z) =
      compose A
        (serreCubeTopCellImage A (homObject A D (F.obj y) (F.obj z)) q (g ≫ F.map y z))
        (serreCubeTopCellImage A (homObject A D (F.obj x) (F.obj y)) p (f ≫ F.map x y))
        (by omega) := by
  exact (congrArg (serreCubeTopCellImage A (homObject A D (F.obj x) (F.obj z)) (p + q))
    (serreCubeComposition_post A F p q f g)).trans
      (serreCubeTopCellImage_composition A p q (f ≫ F.map x y) (g ≫ F.map y z))

end SerrePositivity.KST.SConstruction
