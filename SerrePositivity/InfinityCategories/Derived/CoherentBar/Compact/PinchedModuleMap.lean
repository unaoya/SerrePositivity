module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomModule
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition
public import SerrePositivity.InfinityCategories.Derived.ModuleSphereNaturality
/-!
概要：元の Hom 鎖写像の pinched 空間への作用を単体的加群の射へ持ち上げる。
方針：小さい線形単体への作用を、実 pinched 単体の座標同型で共役する。
規約：元の全単体と鎖写像を保持し、対象の Small 性は要求しない。
使われ方：実評価の脚と Moore ホモロジーチャートの自然性を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

/-- 小さい線形 Hom 模型への、元の鎖写像の全単体的加群作用。 -/
def dgBarCompactLinearHomModuleMap (φ : homObject R D x y ⟶ homObject R E a b) :
    homModule (R := R) x y ⟶ homModule (R := R) a b where
  app _ := ModuleCat.ofHom (pinchedLinearSimplexMap φ)
  naturality {m n} α := by
    ext s
    exact pinchedLinearSimplexMap_pullback φ α.unop.toOrderHom s

/-- 実 pinched 空間の線形化に載った、同じ鎖写像の作用。 -/
def dgBarCompactPinchedModuleMap (φ : homObject R D x y ⟶ homObject R E a b) :
    pinchedHomModule (S := R) x y ⟶ pinchedHomModule (S := R) a b :=
  (pinchedHomModuleCoordinateIso (S := R) x y).hom ≫
    Functor.whiskerRight (dgBarCompactLinearHomModuleMap φ) (ModuleCat.uliftFunctor.{v} R) ≫
      (pinchedHomModuleCoordinateIso (S := R) a b).inv

lemma dgBarCompactPinchedModuleMap_coordinate
    (φ : homObject R D x y ⟶ homObject R E a b) :
    dgBarCompactPinchedModuleMap φ ≫ (pinchedHomModuleCoordinateIso (S := R) a b).hom =
      (pinchedHomModuleCoordinateIso (S := R) x y).hom ≫
        Functor.whiskerRight (dgBarCompactLinearHomModuleMap φ)
          (ModuleCat.uliftFunctor.{v} R) := by
  simp only [dgBarCompactPinchedModuleMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 忘却後の射は元の実 pinched 写像と、全単体で厳密に一致する。 -/
lemma dgBarCompactPinchedModuleMap_forget
    (φ : homObject R D x y ⟶ homObject R E a b) :
    moduleUnderlyingSSetMap (dgBarCompactPinchedModuleMap φ) ≫
      (pinchedHomModuleForgetIso (S := R) a b).hom =
        (pinchedHomModuleForgetIso (S := R) x y).hom ≫ pinchedHomChainMap φ := by
  ext n s
  rw [NatTrans.comp_app, NatTrans.comp_app]
  change (pinchedHomModuleForgetIso (S := R) a b).hom.app n
    ((dgBarCompactPinchedModuleMap φ).app n s) =
      (pinchedHomChainMap φ).app n ((pinchedHomModuleForgetIso (S := R) x y).hom.app n s)
  rw [pinchedHomModuleForgetIso_apply, pinchedHomModuleForgetIso_apply]
  apply (pinchedHomCoordinateEquiv (S := R) a b n).injective
  change ULift.up (toLinearSimplex
    (((pinchedHomCoordinateModuleIso (S := R) x y n).hom ≫
      (ModuleCat.uliftFunctor.{v} R).map ((dgBarCompactLinearHomModuleMap φ).app n) ≫
        (pinchedHomCoordinateModuleIso (S := R) a b n).inv) s)) =
    ULift.up (toLinearSimplex (pinchedHomChainMapSimplex φ s))
  rw [pinchedHomChainMapSimplex_linear]
  change (pinchedHomCoordinateLinearEquiv (S := R) a b n)
    ((pinchedHomCoordinateLinearEquiv (S := R) a b n).symm
      (ULift.up (pinchedLinearSimplexMap φ (toLinearSimplex s)))) = _
  exact (pinchedHomCoordinateLinearEquiv (S := R) a b n).apply_symm_apply _

end SerrePositivity.InfinityCategories
