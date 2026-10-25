module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanEvaluation
public import SerrePositivity.DifferentialGraded.Module.Cone
/-!
概要：主 Hom の Maurer–Cartan 要素で右 dg 加群の微分を変更する。
方針：各評価の MC 複体と、同じ全次数 cochain を持つ作用鎖写像を組み合わせる。
規約：追加微分の閉性と二乗零を個別に要求せず、元の dg 作用を保持する。
使われ方：高次 coherent 図式の bar 余極限を実 dg 加群として構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (M : RightModule R D) (θ : (moduleHom R D M M).X 1)
  (hθ : (moduleHom R D M M).d 1 2 θ +
    compose R (x := M) (y := M) (z := M) θ θ (show (1 : ℤ) + 1 = 2 from rfl) = 0)

abbrev moduleMaurerCartanValue (x : Dᵒᵖ) : Complex R :=
  maurerCartanPerturbComplex (M.obj x) ((moduleHomπ R D M M x.unop).f 1 θ)
    (moduleMaurerCartan_evaluation R D M θ hθ x.unop)

def moduleMaurerCartanMap (x y : Dᵒᵖ) :
    (x ⟶[Complex R] y) ⟶ homComplex R (moduleMaurerCartanValue R D M θ hθ x)
      (moduleMaurerCartanValue R D M θ hθ y) :=
  maurerCartanPerturbHomMap _ _
    (moduleMaurerCartan_evaluation R D M θ hθ x.unop)
    (moduleMaurerCartan_evaluation R D M θ hθ y.unop)
    _ (M.map x y) (moduleMaurerCartan_action R D M θ x y)

@[simp] lemma moduleMaurerCartanMap_v (x y : Dᵒᵖ) (p : ℤ)
    (a : GradedHom R x y p) (i j : ℤ) (hij : i + p = j) :
    ((moduleMaurerCartanMap R D M θ hθ x y).f p a).v i j hij =
      ((M.map x y).f p a).v i j hij := rfl

/-- 全次数作用を保持した実右 dg 加群。 -/
def moduleMaurerCartan : RightModule R D where
  obj := moduleMaurerCartanValue R D M θ hθ
  map := moduleMaurerCartanMap R D M θ hθ
  map_id x := by
    apply (unitCycleEquiv _).injective
    apply Subtype.ext
    change (cycleFromUnit _ (eId (Complex R) x ≫
      moduleMaurerCartanMap R D M θ hθ x x)).val =
        (cycleFromUnit _ (identity (moduleMaurerCartanValue R D M θ hθ x))).val
    rw [cycleFromUnit_postcomp]
    change (moduleMaurerCartanMap R D M θ hθ x x).f 0 (unitElement R x).val =
      (cycleFromUnit _ (identity (moduleMaurerCartanValue R D M θ hθ x))).val
    simp only [identity, cycleFromUnit_unitFromCycle]
    apply Cochain.ext
    intro i j hij
    rw [moduleMaurerCartanMap_v, moduleMap_unit_cochain]
    rfl
  map_comp x y z := by
    apply tensorHom_ext
    intro p q n hn
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro f g
    change (moduleMaurerCartanMap R D M θ hθ x z).f n (forward R f g hn) =
      (enrichedComposition _ _ _).f n
        ((moduleMaurerCartanMap R D M θ hθ x y ⊗ₘ
          moduleMaurerCartanMap R D M θ hθ y z).f n
            (ιTensorObj (x ⟶[Complex R] y) (y ⟶[Complex R] z)
              p q n hn (f ⊗ₜ[R] g)))
    rw [tensorMap_apply, enrichedComposition_apply]
    apply Cochain.ext
    intro i j hij
    rw [moduleMaurerCartanMap_v, moduleMap_forward]
    simp only [Cochain.units_smul_v]
    rw [Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
    rw [Cochain.comp_v _ _ hn i (i + p) j rfl (by omega)]
    simp only [moduleMaurerCartanMap_v]

end SerrePositivity.DifferentialGraded
