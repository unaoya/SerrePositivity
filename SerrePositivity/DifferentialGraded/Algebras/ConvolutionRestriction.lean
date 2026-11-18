module

public import SerrePositivity.DifferentialGraded.Algebras.ConvolutionTensorMaps

/-!
概要：実余モノイドから dg 代数の内部 Hom 畳み込みを構成する。
方針：tensor の oplax 構造と右随伴による転置を使う。
規約：構造は明示的に選び、大域 instance と KST への依存を追加しない。
使われ方：AW 区間の実 dg 代数 path object と転送モデル構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.CategoryTheory.ComonObj _root_.CategoryTheory.MonObj
open _root_.SerrePositivity.DifferentialGraded
namespace SerrePositivity.DGAlgebra
attribute [local instance] _root_.SerrePositivity.DGAlgebra.coalgebraConstant_oplax _root_.SerrePositivity.DGAlgebra.coalgebraTensor_oplax _root_.SerrePositivity.DGAlgebra.coalgebraHomLax

variable (R : Type u) [CommRing R] {H K : Comon (Complex R)}

/-- 概要：畳み込みの convolutionRestriction_one を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionRestriction_one (f : H ⟶ K) (B : Mon (Complex R)) :
    η[((_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R K).obj B).X] ≫ (MonoidalClosed.pre f.hom).app B.X =
      η[((_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R H).obj B).X] := by
  rw [_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor_one, _root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor_one,
    _root_.SerrePositivity.DGAlgebra.coalgebraHomAdjunction_homEquiv, _root_.SerrePositivity.DGAlgebra.coalgebraHomAdjunction_homEquiv,
    MonoidalClosed.curry_pre_app]
  congr 1
  rw [← Category.assoc, _root_.SerrePositivity.DGAlgebra.coalgebraTensor_pre_eta]


variable (R : Type u) [CommRing R] {H K : Comon (Complex R)}

/-- 概要：畳み込みの convolutionRestriction_mul を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionRestriction_mul (f : H ⟶ K) (B : Mon (Complex R)) :
    μ[((_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R K).obj B).X] ≫ (MonoidalClosed.pre f.hom).app B.X =
      ((MonoidalClosed.pre f.hom).app B.X ⊗ₘ (MonoidalClosed.pre f.hom).app B.X) ≫
        μ[((_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R H).obj B).X] := by
  let p := (MonoidalClosed.pre f.hom).app B.X
  have hn : H.X ◁ (p ⊗ₘ p) ≫ Functor.OplaxMonoidal.δ (_root_.SerrePositivity.DGAlgebra.coalgebraTensor R H)
      ((ihom H.X).obj B.X) ((ihom H.X).obj B.X) =
      Functor.OplaxMonoidal.δ (_root_.SerrePositivity.DGAlgebra.coalgebraTensor R H)
        ((ihom K.X).obj B.X) ((ihom K.X).obj B.X) ≫
        (H.X ◁ p ⊗ₘ H.X ◁ p) := by
    simpa [_root_.SerrePositivity.DGAlgebra.coalgebraTensor, _root_.SerrePositivity.DGAlgebra.coalgebraConstant] using
      (Functor.OplaxMonoidal.δ_natural (_root_.SerrePositivity.DGAlgebra.coalgebraTensor R H) p p).symm
  have he : H.X ◁ p ≫ (ihom.ev H.X).app B.X =
      f.hom ▷ ((ihom K.X).obj B.X) ≫ (ihom.ev K.X).app B.X :=
    MonoidalClosed.id_tensor_pre_app_comp_ev f.hom B.X
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_left,
    _root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor_mul, _root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor_mul,
    _root_.SerrePositivity.DGAlgebra.coalgebraHomAdjunction_homEquiv, _root_.SerrePositivity.DGAlgebra.coalgebraHomAdjunction_homEquiv,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry,
    _root_.SerrePositivity.DGAlgebra.coalgebraHomAdjunction_counit, _root_.SerrePositivity.DGAlgebra.coalgebraHomAdjunction_counit]
  change f.hom ▷ _ ≫ _ ≫ _ ≫ B.mon.mul = H.X ◁ (p ⊗ₘ p) ≫ _ ≫ _ ≫ B.mon.mul
  rw [← Category.assoc (H.X ◁ (p ⊗ₘ p)), hn]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, he, ← tensorHom_comp_tensorHom_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ ((ihom.ev K.X).app B.X ⊗ₘ (ihom.ev K.X).app B.X) ≫ B.mon.mul)
    (_root_.SerrePositivity.DGAlgebra.coalgebraTensor_pre_delta R f ((ihom K.X).obj B.X) ((ihom K.X).obj B.X))


variable (R : Type u) [CommRing R]

/-- 概要：畳み込みの convolutionRestriction を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def convolutionRestriction {H K : Comon (Complex R)} (f : H ⟶ K) (B : Mon (Complex R)) :
    (_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R K).obj B ⟶ (_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R H).obj B :=
  Mon.Hom.mk' ((MonoidalClosed.pre f.hom).app B.X)
    (_root_.SerrePositivity.DGAlgebra.convolutionRestriction_one R f B) (_root_.SerrePositivity.DGAlgebra.convolutionRestriction_mul R f B)

/-- 概要：畳み込みの convolutionRestriction_hom を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma convolutionRestriction_hom {H K : Comon (Complex R)} (f : H ⟶ K)
    (B : Mon (Complex R)) :
    (_root_.SerrePositivity.DGAlgebra.convolutionRestriction R f B).hom = (MonoidalClosed.pre f.hom).app B.X := rfl

/-- 概要：畳み込みの convolutionRestrictionNatTrans を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def convolutionRestrictionNatTrans {H K : Comon (Complex R)} (f : H ⟶ K) :
    _root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R K ⟶ _root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R H where
  app := _root_.SerrePositivity.DGAlgebra.convolutionRestriction R f
  naturality _ _ g := by
    apply Mon.Hom.ext'
    exact (MonoidalClosed.pre f.hom).naturality g.hom

/-- 概要：畳み込みの convolutionAlgebraContravariant を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def convolutionAlgebraContravariant (B : Mon (Complex R)) :
    (Comon (Complex R))ᵒᵖ ⥤ Mon (Complex R) where
  obj H := (_root_.SerrePositivity.DGAlgebra.convolutionAlgebraFunctor R H.unop).obj B
  map f := _root_.SerrePositivity.DGAlgebra.convolutionRestriction R f.unop B
  map_id H := by
    apply Mon.Hom.ext'
    change (MonoidalClosed.pre (𝟙 H.unop.X)).app B.X = 𝟙 _
    rw [MonoidalClosed.pre_id]
    rfl
  map_comp f g := by
    apply Mon.Hom.ext'
    change (MonoidalClosed.pre (g.unop.hom ≫ f.unop.hom)).app B.X =
      (MonoidalClosed.pre f.unop.hom).app B.X ≫ (MonoidalClosed.pre g.unop.hom).app B.X
    rw [MonoidalClosed.pre_map]
    rfl


end SerrePositivity.DGAlgebra
