module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# 独立な二つの群作用の余不変

HA 3.2.4.7 の自由比較のテンソル側で使う。直積群が左右の因子に独立に作用するとき、
テンソルの余不変は各因子の余不変のテンソルに一致する。群の有限性や平坦性は不要。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory Representation
open scoped TensorProduct
variable {A G H : Type u} [CommRing A] [Group G] [Group H]
  (V : Rep.{u} A G) (W : Rep.{u} A H)

/-- 左右の群が、それぞれの因子に独立に作用するテンソル表現。 -/
abbrev externalTensorRepresentation : Rep.{u} A (G × H) :=
  Rep.res (MonoidHom.fst G H) V ⊗ Rep.res (MonoidHom.snd G H) W

/-- 直積群の余不変から、左右それぞれの余不変のテンソルへの指定射。 -/
def productCoinvariantsHom :
    (externalTensorRepresentation V W).ρ.Coinvariants →ₗ[A]
      V.ρ.Coinvariants ⊗[A] W.ρ.Coinvariants :=
  Coinvariants.lift _ (TensorProduct.map (Coinvariants.mk V.ρ) (Coinvariants.mk W.ρ)) (by
    intro g
    apply TensorProduct.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    simp [externalTensorRepresentation, Representation.tprod_apply])

/-- 左の作用だけで商を取った、指定された双線形写像。 -/
def productCoinvariantsLeft : V.ρ.Coinvariants →ₗ[A] W →ₗ[A]
    (externalTensorRepresentation V W).ρ.Coinvariants :=
  Coinvariants.lift V.ρ
    (Rep.coinvariantsTensorMk (Rep.res (MonoidHom.fst G H) V)
      (Rep.res (MonoidHom.snd G H) W)) (by
    intro g
    ext v w
    have h := Coinvariants.mk_self_apply (externalTensorRepresentation V W).ρ (g, 1)
      (v ⊗ₜ[A] w)
    simpa [externalTensorRepresentation, Rep.coinvariantsTensorMk, Representation.tprod_apply]
      using h)

/-- さらに右の作用で商を取り、左右の余不変のテンソルからの指定射を得る。 -/
def productCoinvariantsInv :
    V.ρ.Coinvariants ⊗[A] W.ρ.Coinvariants →ₗ[A]
      (externalTensorRepresentation V W).ρ.Coinvariants :=
  TensorProduct.lift (LinearMap.flip (Coinvariants.lift W.ρ
    (productCoinvariantsLeft V W).flip (by
      intro h
      apply LinearMap.ext
      intro w
      apply Coinvariants.hom_ext
      ext v
      have hh := Coinvariants.mk_self_apply (externalTensorRepresentation V W).ρ (1, h)
        (v ⊗ₜ[A] w)
      simpa [productCoinvariantsLeft, externalTensorRepresentation, Rep.coinvariantsTensorMk,
        Representation.tprod_apply] using hh)))

/-- 元のテンソルの生成元で、順射は左右の指定商写像のテンソルである。 -/
lemma productCoinvariantsHom_mk (v : V) (w : W) :
    productCoinvariantsHom V W (Coinvariants.mk _ (v ⊗ₜ[A] w)) =
      Coinvariants.mk V.ρ v ⊗ₜ[A] Coinvariants.mk W.ρ w := rfl

/-- 左右の商の生成元で、逆射は元の直積群の商写像である。 -/
lemma productCoinvariantsInv_mk (v : V) (w : W) :
    productCoinvariantsInv V W (Coinvariants.mk V.ρ v ⊗ₜ[A] Coinvariants.mk W.ρ w) =
      Coinvariants.mk _ (v ⊗ₜ[A] w) := rfl

/-- 独立な二つの群作用について、指定された生成元を保つ余不変の同型。 -/
def productCoinvariantsIso :
    ModuleCat.of A (externalTensorRepresentation V W).ρ.Coinvariants ≅
      ModuleCat.of A (V.ρ.Coinvariants ⊗[A] W.ρ.Coinvariants) where
  hom := ModuleCat.ofHom (productCoinvariantsHom V W)
  inv := ModuleCat.ofHom (productCoinvariantsInv V W)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply Coinvariants.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply Coinvariants.hom_ext
    apply LinearMap.ext
    intro v
    apply Coinvariants.hom_ext
    apply LinearMap.ext
    intro w
    rfl

/-- 指定された分離同型は、左右両方の表現の射について自然である。 -/
lemma productCoinvariantsIso_naturality {V' : Rep.{u} A G} {W' : Rep.{u} A H}
    (f : V ⟶ V') (g : W ⟶ W') :
    (Rep.coinvariantsFunctor A (G × H)).map
        ((Rep.resMap (MonoidHom.fst G H) f) ⊗ₘ (Rep.resMap (MonoidHom.snd G H) g)) ≫
      (productCoinvariantsIso V' W').hom =
    (productCoinvariantsIso V W).hom ≫
      ((Rep.coinvariantsFunctor A G).map f ⊗ₘ (Rep.coinvariantsFunctor A H).map g) := by
  apply ModuleCat.hom_ext
  apply Coinvariants.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  rfl

end SerrePositivity.EInfinity
