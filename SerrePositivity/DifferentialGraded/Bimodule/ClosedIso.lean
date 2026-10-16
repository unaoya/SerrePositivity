module
public import SerrePositivity.DifferentialGraded.Bimodule.ClosedTransforms
public import SerrePositivity.DifferentialGraded.Module.HomIsoSquare

/-! # 全Hom自然なbimodule同型族の順逆の閉零変換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma isoFamily_inv_naturality {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c c' : C) :
    N.toFunctor.map c c' ≫
      moduleHomPostcompose A B (N.rightAt c) (N.rightAt c') (M.rightAt c') (a c').inv =
    M.toFunctor.map c c' ≫
      moduleHomPrecompose A B (N.rightAt c) (M.rightAt c) (M.rightAt c') (a c).inv := by
  exact moduleHom_iso_square_inv A B (M.toFunctor.map c c') (N.toFunctor.map c c')
    (a c) (a c') (h c c')

/-- 全Hom自然な右加群同型族の順方向の単位パラメータ変換。 -/
def isoFamilyHom {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    : BimoduleParamTrans A B C (𝟙_ (Complex A)) M N :=
  closedFamilyTrans A B C (fun c => (a c).hom) h

/-- 同じ同型族の逆方向も全Homに関して豊穣自然。 -/
def isoFamilyInv {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    : BimoduleParamTrans A B C (𝟙_ (Complex A)) N M :=
  closedFamilyTrans A B C (fun c => (a c).inv) (isoFamily_inv_naturality A B C a h)

@[simp]
lemma isoFamilyHom_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (isoFamilyHom A B C a h).app c =
      ForgetEnrichment.homTo (Complex A) (a c).hom := rfl

@[simp]
lemma isoFamilyInv_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (isoFamilyInv A B C a h).app c =
      ForgetEnrichment.homTo (Complex A) (a c).inv := rfl

/-- 順逆の成分合成は主Homの閉単位元に一致する。 -/
lemma isoFamily_hom_inv_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((isoFamilyHom A B C a h).app c ⊗ₘ (isoFamilyInv A B C a h).app c) ≫
      eComp (Complex A) (M.rightAt c) (N.rightAt c) (M.rightAt c) =
      eId (Complex A) (M.rightAt c) :=
  moduleIso_closed_hom_inv A B (a c)

/-- 順逆の成分合成は主Homの閉単位元に一致する。 -/
lemma isoFamily_inv_hom_app {M N : Bimodule A B C}
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ≅
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (h : ∀ c c', M.toFunctor.map c c' ≫
      moduleHomPostcompose A B (M.rightAt c) (M.rightAt c') (N.rightAt c') (a c').hom =
      N.toFunctor.map c c' ≫
      moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N.rightAt c') (a c).hom)
    (c : C) :
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((isoFamilyInv A B C a h).app c ⊗ₘ (isoFamilyHom A B C a h).app c) ≫
      eComp (Complex A) (N.rightAt c) (M.rightAt c) (N.rightAt c) =
      eId (Complex A) (N.rightAt c) :=
  moduleIso_closed_hom_inv A B (a c).symm

end SerrePositivity.DifferentialGraded.Bimodule
