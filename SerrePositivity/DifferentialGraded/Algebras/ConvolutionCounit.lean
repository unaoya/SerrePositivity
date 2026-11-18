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

private lemma unitTensorCoherence {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C] (X Y : C) :
    ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ (𝟙_ C) X (𝟙_ C) Y ≫
      ((λ_ X).hom ⊗ₘ (λ_ Y).hom) = (λ_ (X ⊗ Y)).hom := by
  rw [leftUnitor_monoidal]
  simp only [tensorHom_id, tensorδ_tensorμ_assoc,
    ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

private lemma counitTensorCoherence {C : Type v} [Category.{w} C] [MonoidalCategory C]
    [BraidedCategory C] (H : Comon C) (X Y : C) :
    (Δ[H.X] ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ H.X X H.X Y ≫
      ((ε[H.X] ▷ X ≫ (λ_ X).hom) ⊗ₘ (ε[H.X] ▷ Y ≫ (λ_ Y).hom)) =
      ε[H.X] ▷ (X ⊗ Y) ≫ (λ_ (X ⊗ Y)).hom := by
  let : MonoidalCategory (C × C) := MonoidalCategory.prodMonoidal C C
  have hn : tensorδ H.X X H.X Y ≫ (ε[H.X] ▷ X ⊗ₘ ε[H.X] ▷ Y) =
      ((ε[H.X] ⊗ₘ ε[H.X]) ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ (𝟙_ C) X (𝟙_ C) Y := by
    simpa using (Functor.OplaxMonoidal.δ_natural (tensor C)
      (show (H.X, X) ⟶ (𝟙_ C, X) from (ε[H.X], 𝟙 X))
      (show (H.X, Y) ⟶ (𝟙_ C, Y) from (ε[H.X], 𝟙 Y)))
  have hc := (IsComonHom.hom_comul (default : H ⟶ Comon.trivial C).hom).symm
  change Δ[H.X] ≫ (ε[H.X] ⊗ₘ ε[H.X]) = ε[H.X] ≫ (λ_ (𝟙_ C)).inv at hc
  have hp := congrArg (fun t => (Δ[H.X] ⊗ₘ 𝟙 (X ⊗ Y)) ≫ t ≫
    ((λ_ X).hom ⊗ₘ (λ_ Y).hom)) hn
  simp only [Category.assoc] at hp
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, hc] at hp
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc] at hp
  have hu := _root_.SerrePositivity.DGAlgebra.unitTensorCoherence X Y
  simp only [tensorHom_id] at hu
  rw [hu] at hp
  simpa only [tensorHom_id, ← tensorHom_comp_tensorHom, Category.assoc] using hp

variable (R : Type u) [CommRing R]

/-- 概要：畳み込みの coalgebraTensorCounit を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
def coalgebraTensorCounit (H : Comon (Complex R)) : _root_.SerrePositivity.DGAlgebra.coalgebraTensor R H ⟶ 𝟭 (Complex R) :=
  (_root_.SerrePositivity.DGAlgebra.coalgebraTensorIso R H).inv ≫ (tensoringLeft (Complex R)).map ε[H.X] ≫
    (leftUnitorNatIso (Complex R)).hom

/-- 概要：畳み込みの coalgebraTensorCounit_app を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensorCounit_app (H : Comon (Complex R)) (X : Complex R) :
    (_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app X = ε[H.X] ▷ X ≫ (λ_ X).hom := by
  change (𝟙 _) ≫ ε[H.X] ▷ X ≫ (λ_ X).hom = _
  exact Category.id_comp _

/-- 概要：畳み込みの coalgebraTensorCounit_unit を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensorCounit_unit (H : Comon (Complex R)) :
    Functor.OplaxMonoidal.η (_root_.SerrePositivity.DGAlgebra.coalgebraTensor R H) =
      (_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app (𝟙_ (Complex R)) := by
  rw [_root_.SerrePositivity.DGAlgebra.coalgebraTensor_eta, _root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit_app]
  simp only [tensorHom_id]

/-- 概要：畳み込みの coalgebraTensorCounit_tensor を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensorCounit_tensor (H : Comon (Complex R)) (X Y : Complex R) :
    Functor.OplaxMonoidal.δ (_root_.SerrePositivity.DGAlgebra.coalgebraTensor R H) X Y ≫
      ((_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app X ⊗ₘ (_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app Y) =
      (_root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit R H).app (X ⊗ Y) := by
  rw [_root_.SerrePositivity.DGAlgebra.coalgebraTensor_delta, _root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit_app,
    _root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit_app, _root_.SerrePositivity.DGAlgebra.coalgebraTensorCounit_app]
  simpa only [_root_.SerrePositivity.DGAlgebra.coalgebraTensor, _root_.SerrePositivity.DGAlgebra.coalgebraConstant, Functor.comp_obj, Functor.prod'_obj,
    Functor.id_obj, Functor.const_obj_obj, tensor_obj, Category.assoc] using
    (_root_.SerrePositivity.DGAlgebra.counitTensorCoherence H X Y)


end SerrePositivity.DGAlgebra
