module

public import SerrePositivity.EInfinity.DGAlgebra.Convolution

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
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped ComonObj MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.EInfinity.DGAlgebra
attribute [local instance] coalgebraConstant_oplax coalgebraTensor_oplax coalgebraHomLax

variable (R : Type u) [CommRing R]
local instance : MonoidalCategory (Complex R × Complex R) :=
  MonoidalCategory.prodMonoidal (Complex R) (Complex R)

/-- 概要：畳み込みの coalgebraTensor_eta を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensor_eta (H : Comon (Complex R)) :
    Functor.OplaxMonoidal.η (coalgebraTensor R H) =
      (ε[H.X] ⊗ₘ 𝟙 (𝟙_ (Complex R))) ≫ (λ_ (𝟙_ (Complex R))).hom := by
  simp [coalgebraTensor, Functor.OplaxMonoidal.comp_η,
    tensor_map]
  rfl

/-- 概要：畳み込みの coalgebraTensor_delta を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensor_delta (H : Comon (Complex R)) (X Y : Complex R) :
    Functor.OplaxMonoidal.δ (coalgebraTensor R H) X Y =
      (Δ[H.X] ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ H.X X H.X Y := by
  simp [coalgebraTensor, Functor.OplaxMonoidal.comp_δ,
    tensor_map]
  rfl

/-- 概要：畳み込みの coalgebraTensor_eta_counit を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensor_eta_counit (H : Comon (Complex R)) :
    Functor.OplaxMonoidal.η (coalgebraTensor R H) = (ρ_ H.X).hom ≫ ε[H.X] := by
  rw [coalgebraTensor_eta]
  simp [unitors_equal]

/-- 概要：畳み込みの coalgebraTensor_pre_eta を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensor_pre_eta {H K : Comon (Complex R)} (f : H ⟶ K) :
    f.hom ▷ (𝟙_ (Complex R)) ≫ Functor.OplaxMonoidal.η (coalgebraTensor R K) =
      Functor.OplaxMonoidal.η (coalgebraTensor R H) := by
  rw [coalgebraTensor_eta_counit, coalgebraTensor_eta_counit,
    ← Category.assoc, rightUnitor_naturality]
  simp

/-- 概要：畳み込みの coalgebraTensor_pre_delta を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraTensor_pre_delta {H K : Comon (Complex R)} (f : H ⟶ K)
    (X Y : Complex R) :
    f.hom ▷ (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ (coalgebraTensor R K) X Y =
      Functor.OplaxMonoidal.δ (coalgebraTensor R H) X Y ≫
        (f.hom ▷ X ⊗ₘ f.hom ▷ Y) := by
  have ht : tensorδ H.X X H.X Y ≫ (f.hom ▷ X ⊗ₘ f.hom ▷ Y) =
      ((f.hom ⊗ₘ f.hom) ⊗ₘ 𝟙 (X ⊗ Y)) ≫ tensorδ K.X X K.X Y := by
    simpa using (Functor.OplaxMonoidal.δ_natural (tensor (Complex R))
      (show (H.X, X) ⟶ (K.X, X) from (f.hom, 𝟙 X))
      (show (H.X, Y) ⟶ (K.X, Y) from (f.hom, 𝟙 Y)))
  simp only [tensorHom_id] at ht
  rw [coalgebraTensor_delta, coalgebraTensor_delta]
  simp only [tensorHom_id]
  rw [← comp_whiskerRight_assoc, IsComonHom.hom_comul, comp_whiskerRight,
    Category.assoc, ← ht]
  simp only [Category.assoc]


variable (R : Type u) [CommRing R]

/-- 概要：畳み込みの coalgebraHomAdjunction_homEquiv を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraHomAdjunction_homEquiv (H : Comon (Complex R))
    (X Y : Complex R) (t : (coalgebraTensor R H).obj X ⟶ Y) :
    (coalgebraHomAdjunction R H).homEquiv X Y t = MonoidalClosed.curry (A := H.X) t := by
  rw [coalgebraHomAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  change (ihom.adjunction H.X).homEquiv X Y ((𝟙 _) ≫ t) = _
  rw [Category.id_comp]
  rfl

/-- 概要：畳み込みの coalgebraHomAdjunction_counit を与える。
方針：元の余モノイドと閉構造の自然性を使う。
規約：底の複体と射を保持する。使われ方：実 AW path object の構成。 -/
lemma coalgebraHomAdjunction_counit (H : Comon (Complex R)) (B : Complex R) :
    (coalgebraHomAdjunction R H).counit.app B = (ihom.ev H.X).app B := by
  change (coalgebraTensorIso R H).inv.app _ ≫ (ihom.adjunction H.X).counit.app B = _
  change (𝟙 _) ≫ (ihom.ev H.X).app B = _
  exact Category.id_comp _


end SerrePositivity.EInfinity.DGAlgebra
