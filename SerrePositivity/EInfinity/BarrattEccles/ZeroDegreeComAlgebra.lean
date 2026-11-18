module

public import SerrePositivity.EInfinity.BarrattEccles.ZeroDegreeAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraOperadEpi
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIso

/-!
# 零次集中 E 代数の元の底の Com 代数構造

概要：同じ実 augmentation に沿って元の零次集中 E 作用を Com の全作用へ降ろす。
方針：実切断による augmentation の全射性と全 arity の厳密な因子化を使う。
規約：元の底の複体を変えず、制限すると元の E 代数と同型になる。
使われ方：通常の可換代数の離散像との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

lemma augmentation_epi (n : ℕ) : Epi ((augmentation A).map.app (FiniteBijection.of n)) :=
  epi_of_epi_fac (aritySection_augmentation A n)

variable (B : (operad A).Algebra) [B.carrier.IsStrictlyLE 0] [B.carrier.IsStrictlyGE 0]

def zeroDegreeComAlgebra : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A).Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofOperadEpi (augmentation A) (augmentation_epi A) B
    (zeroDegreeComAction B) (zeroDegreeAction_factor B)

def zeroDegreeComRestrictionIso :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj (augmentation A) (zeroDegreeComAlgebra A B) ≅ B := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso
    (X := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebraObj (augmentation A) (zeroDegreeComAlgebra A B))
    (Y := B) (Iso.refl B.carrier)
  intro n
  change (((augmentation A).map.app (FiniteBijection.of n) ▷ power B.carrier n) ≫
    zeroDegreeComAction B n) ≫ 𝟙 B.carrier =
      (𝟙 ((operad A).arity n) ⊗ₘ TensorPowers.map (𝟙 B.carrier) n) ≫ B.action n
  simp only [Category.comp_id, TensorPowers.map_id, tensorHom_id, id_whiskerRight,
    Category.id_comp]
  exact zeroDegreeAction_factor B n

end SerrePositivity.EInfinity.BarrattEccles
