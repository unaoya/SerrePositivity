module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
概要：非有界複体の Hom の試験対象に関する反変自然性。
方針：既存の前合成と後合成の可換性を、同じ cochain 成分で示す。
規約：既存の homFunctor と homPrecompose をそのまま使う。
使われ方：HA 1.2.4、G10 の Hom 試験のパラメーター自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex HomComplex
namespace SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 前合成と後合成は複体の射として可換。 -/
theorem homPrecompose_postcompose {P Q X Y : Complex A} (g : P ⟶ Q) (f : X ⟶ Y) :
    homPostcompose Q f ≫ homPrecompose g Y = homPrecompose g X ≫ homPostcompose P f := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (Cochain.ofHom g).comp (z.comp (Cochain.ofHom f) (add_zero p)) (zero_add p) =
    ((Cochain.ofHom g).comp z (zero_add p)).comp (Cochain.ofHom f) (add_zero p)
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Category.assoc]

/-- 試験対象の射から得られる Hom 関手間の指定自然変換。 -/
def homPrecomposeNatTrans {P Q : Complex A} (g : P ⟶ Q) : homFunctor Q ⟶ homFunctor P where
  app X := homPrecompose g X
  naturality _ _ f := homPrecompose_postcompose g f

end SerrePositivity.DifferentialGraded
